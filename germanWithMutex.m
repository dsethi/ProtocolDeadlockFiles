const  ---- Configuration parameters ----

  NODE_NUM : 2;
  DATA_NUM : 2;

type   ---- Type declarations ----

  NODE : scalarset(NODE_NUM);
  DATA : scalarset(DATA_NUM);

  ABS_NODE : union {NODE, enum{Other}};
  CACHE_STATE : enum {I, S, E};
  CACHE : record State : CACHE_STATE; Data : DATA; end;

  MSG_CMD : enum {Empty, ReqS, ReqE, Inv, InvAck, GntS, GntE};
  MSG : record Cmd : MSG_CMD; Data : DATA; end;

var   ---- State variables ----

  Cache : array [NODE] of CACHE;      -- Caches
  Chan1 : array [NODE] of MSG;        -- Channels for Req*
  Chan2 : array [NODE] of MSG;        -- Channels for Gnt* and Inv
  Chan3 : array [NODE] of MSG;        -- Channels for InvAck
  InvSet : array [NODE] of boolean;   -- Set of nodes to be invalidated
  ShrSet : array [NODE] of boolean;   -- Set of nodes having S or E copies
  ExGntd : boolean;                   -- E copy has been granted
  CurCmd : MSG_CMD;                   -- Current request command
  CurPtr : ABS_NODE;                  -- Current request node
  MemData : DATA;                     -- Memory data
  AuxData : DATA;                     -- Auxiliary variable for latest data
  AuxLastSharer: ABS_NODE;
  ReqSActive: array [NODE] of Boolean;
  CountInvShr: 0..NODE_NUM+1; -- Counts number of caches with InvSet=1 or ShrSet = 1; +1 done for env agent
  env_o : Boolean;

function absproc (i: ABS_NODE) : BOOLEAN;
  begin
    if i = Other then
    assert false;
      return true;
    else
      return false;
    end;
  end;

function isReqSActive(i: NODE): Boolean;
begin

--return ReqSActive[i];
return true;

endFunction;

function canReqSProgress(i: NODE): Boolean;
begin

return
(Chan1[i].Cmd = Empty & Cache[i].State = I)
|
(CurCmd = Empty & Chan1[i].Cmd = ReqS)
|
(CurCmd = ReqS & CurPtr = i & Chan2[i].Cmd = Empty & ExGntd = false)
|
(Chan2[i].Cmd = GntS);

endFunction;

function canStoreProgress(i: NODE): Boolean;
begin
return Cache[i].State = E;
endFunction;

function canReqEProgress(i: NODE): Boolean;
begin

return
(Chan1[i].Cmd = Empty & (Cache[i].State = I | Cache[i].State = S))
|
(CurCmd = Empty & Chan1[i].Cmd = ReqE)
|
CurCmd = ReqE & CurPtr = i & Chan2[i].Cmd = Empty & ExGntd = false &
  forall j : NODE do ShrSet[j] = false end
|
(Chan2[i].Cmd = GntE);

endFunction;

function canInvalidateProgress(i: NODE): Boolean;
begin

return 
( Chan2[i].Cmd = Empty & InvSet[i] = true &
  ( CurCmd = ReqE | CurCmd = ReqS & ExGntd = true )
)
|
(Chan2[i].Cmd = Inv & Chan3[i].Cmd = Empty)
|
(Chan3[i].Cmd = InvAck & CurCmd != Empty);

endFunction;

function canReqProgress(i: NODE): Boolean;
begin
return canReqEProgress(i)|canReqSProgress(i)|canInvalidateProgress(i)|canStoreProgress(i);
endFunction;

function conflictingReqProgresses(j: NODE): Boolean;
begin
 return canReqEProgress(j)|canReqSProgress(j)|canInvalidateProgress(j);
endFunction;

function conflictingReqProgresses2(j: NODE): Boolean;
begin
--if (InvSetCount>0) then	
--for j: NODE do
-- if (InvSet[j] = true)|(ShrSet[j] = true) then 
    if(Chan2[j].Cmd = Empty) then
      return canInvalidateProgress(j); 
    else
      return canReqEProgress(j)|canReqSProgress(j)|canInvalidateProgress(j);
    endif;
 --endif;
--end;

return false;

endFunction;

function conflictingReqProgresses1(j: NODE): Boolean;
begin
--for j: NODE do
--if(CurPtr=j) then
if (CurCmd = ReqE) then 	       
     return canReqEProgress(j)
--|(((InvSet[k] = true)|(ShrSet[k] = true))->conflictingReqProgresses2(k))
else 
 if (CurCmd = ReqS)
--&(j!=i) 
    then 	       
     return canReqSProgress(j)
--|(((InvSet[k] = true)|(ShrSet[k] = true))->conflictingReqProgresses2(k))
 else
  return false;
 endif;
endif;
--endif;
return false;
--end;
endFunction;

procedure SetShrSetToFalse(i: NODE); 
begin

if(ShrSet[i] = true) then 
 CountInvShr := CountInvShr - 1;
endif;
ShrSet[i] := false; 
AuxLastSharer := i;
endProcedure;

procedure SetShrSetToTrue(i: NODE); 
begin

if(ShrSet[i] = false) then 
 CountInvShr := CountInvShr + 1;
endif;
ShrSet[i] := true; 
AuxLastSharer := i;
endProcedure;

---- Initial states ----

ruleset d : DATA do startstate "Init"
  for i : NODE do
    Chan1[i].Cmd := Empty; Chan2[i].Cmd := Empty; Chan3[i].Cmd := Empty;
    Cache[i].State := I; InvSet[i] := false; ShrSet[i] := false;
    ReqSActive[i] := false;
  end;
  ExGntd := false; CurCmd := Empty; MemData := d; AuxData := d;
  env_o := true;
  CountInvShr := 0;
end end;

---- State transitions ----

ruleset i : NODE; d : DATA do rule "Store"
  Cache[i].State = E
==>
  Cache[i].Data := d; AuxData := d;
end end;

ruleset i : NODE do rule "SendReqSFlowS"
  Chan1[i].Cmd = Empty & Cache[i].State = I
==>
  Chan1[i].Cmd := ReqS;
  ReqSActive[i] := true;
end end;

ruleset i : NODE do rule "SendReqEFlowE"
  Chan1[i].Cmd = Empty & (Cache[i].State = I | Cache[i].State = S)
==>
  Chan1[i].Cmd := ReqE;
end end;

ruleset i : NODE do rule "RecvReqSFlowS"
  CurCmd = Empty & Chan1[i].Cmd = ReqS
==>
  CurCmd := ReqS; CurPtr := i; Chan1[i].Cmd := Empty;
  for j : NODE do InvSet[j] := ShrSet[j] end;
end end;

ruleset i : NODE do rule "RecvReqEFlowE"
  CurCmd = Empty & Chan1[i].Cmd = ReqE
==>
  CurCmd := ReqE; CurPtr := i; Chan1[i].Cmd := Empty;
  for j : NODE do InvSet[j] := ShrSet[j] end;
end end;

ruleset i : NODE do rule "SendInvFlowI"
  Chan2[i].Cmd = Empty & InvSet[i] = true &
  ( CurCmd = ReqE | CurCmd = ReqS & ExGntd = true )
==>
  Chan2[i].Cmd := Inv; InvSet[i] := false;
end end;

ruleset i : NODE do rule "SendInvAckFlowI"
  Chan2[i].Cmd = Inv & Chan3[i].Cmd = Empty
==>
  Chan2[i].Cmd := Empty; Chan3[i].Cmd := InvAck;
  if (Cache[i].State = E) then Chan3[i].Data := Cache[i].Data end;
  Cache[i].State := I; undefine Cache[i].Data;
end end;

ruleset i : NODE do rule "RecvInvAckFlowI"
  Chan3[i].Cmd = InvAck & CurCmd != Empty
==>
  Chan3[i].Cmd := Empty; ShrSet[i] := false;

  undefine AuxLastSharer;
  for p : NODE do
    if (p != i & ShrSet[p]) then
      AuxLastSharer := p;
    end;
  end;

  if (ExGntd = true)
  then ExGntd := false; MemData := Chan3[i].Data; undefine Chan3[i].Data end;
end end;

ruleset i : NODE do rule "SendGntSFlowS"
  CurCmd = ReqS & CurPtr = i & Chan2[i].Cmd = Empty & ExGntd = false
==>
  Chan2[i].Cmd := GntS; Chan2[i].Data := MemData; ShrSet[i] := true; AuxLastSharer := i;
  CurCmd := Empty; undefine CurPtr;
end end;

ruleset i : NODE do rule "SendGntEFlowE"
  CurCmd = ReqE & CurPtr = i & Chan2[i].Cmd = Empty & ExGntd = false &
  forall j : NODE do ShrSet[j] = false end
==>
  Chan2[i].Cmd := GntE; Chan2[i].Data := MemData; ShrSet[i] := true; AuxLastSharer := i;
  ExGntd := true; CurCmd := Empty; undefine CurPtr;
end end;

ruleset i : NODE do rule "RecvGntSFlowS"
  Chan2[i].Cmd = GntS
==>
  Cache[i].State := S; Cache[i].Data := Chan2[i].Data;
  Chan2[i].Cmd := Empty; undefine Chan2[i].Data;
  ReqSActive[i] := false;
end end;

ruleset i : NODE do rule "RecvGntEFlowE"
  Chan2[i].Cmd = GntE
==>
  Cache[i].State := E; Cache[i].Data := Chan2[i].Data;
  Chan2[i].Cmd := Empty; undefine Chan2[i].Data;
end end;

---- Invariant properties ----

invariant "CntrlProp"
  forall i : NODE do forall j : NODE do
    i != j -> (Cache[i].State = E -> Cache[j].State = I) &
              (Cache[i].State = S -> Cache[j].State = I | Cache[j].State = S)
  end end;

invariant "DataProp"
  ( ExGntd = false -> MemData = AuxData ) &
  forall i : NODE do Cache[i].State != I -> Cache[i].Data = AuxData end;

---- Abstract state transitions ----

rule "ABS_Skip" end;

ruleset d : DATA do rule "ABS_Store"
env_o &  true

& ExGntd = true &

  forall j : NODE do
    Cache[j].State = I &
    Chan2[j].Cmd != GntS &
    Chan2[j].Cmd != GntE &
    Chan3[j].Cmd != InvAck
  end
==>
  AuxData := d;
end end;

rule "ABS_RecvReqS"
env_o & CurCmd = Empty
==>
  CurCmd := ReqS; CurPtr := Other;
  for j : NODE do InvSet[j] := ShrSet[j] end;
end;

rule "ABS_RecvReqE"
env_o & CurCmd = Empty
==>
  CurCmd := ReqE; CurPtr := Other;
  for j : NODE do InvSet[j] := ShrSet[j] end;
end;

rule "ABS_RecvInvAck"
env_o & CurCmd != Empty & ExGntd = true &

  forall j : NODE do
    Cache[j].State != E &
    Chan2[j].Cmd != GntE &

    Chan3[j].Cmd != InvAck
  end
==>
  ExGntd := false;

  undefine AuxLastSharer;
  for p : NODE do
    if (ShrSet[p]) then
      AuxLastSharer := p;
    end;
  end;

--    undefine MemData;
  MemData := AuxData;
end;

rule "ABS_SendGntS"
env_o & CurCmd = ReqS & CurPtr = Other & ExGntd = false
==>
  CurCmd := Empty; undefine CurPtr; AuxLastSharer := Other;
end;

rule "ABS_SendGntE"
env_o & CurCmd = ReqE & CurPtr = Other & ExGntd = false &
  forall j : NODE do ShrSet[j] = false end
==>
  ExGntd := true; CurCmd := Empty; undefine CurPtr; AuxLastSharer := Other;
end;

---- Noninterference lemmas ----

invariant "Lemma_1"
  forall i : NODE do
    Chan3[i].Cmd = InvAck & CurCmd != Empty & ExGntd = true ->
    Chan3[i].Data = AuxData &   -- 5
    forall j : NODE do
      j != i -> Cache[j].State != E &   -- 1
                Chan2[j].Cmd != GntE &  -- 1
                Chan3[j].Cmd != InvAck  -- 2
    end
  end;

invariant "Lemma_2"
  forall i : NODE do
    Cache[i].State = E ->
    ExGntd = true &   -- 4
    forall j : NODE do
      j != i -> Cache[j].State = I &     -- 6
                Chan2[j].Cmd != GntS &   -- 6
                Chan2[j].Cmd != GntE &   -- 6
                Chan3[j].Cmd != InvAck   -- 7
    end
  end;



invariant "ProgressOfReqInit"
forall i : NODE do  
  ((isUndefined(CurPtr)) -> (canReqProgress(i)))
end;


invariant "ProgressOfActiveReq"
forall i : NODE do  
  (((!isUndefined(CurPtr))&(CurPtr=i)&(!((CurCmd=ReqE)|((CurCmd=ReqS)&ExGntd)))) -> (canReqProgress(i)))
end;

/*
invariant "Interactions"
forall i:NODE do
  forall j: NODE do
    ((!isUndefined(CurPtr))&(CurPtr=i)&((CurCmd=ReqE)|((CurCmd=ReqS)&ExGntd))&(ShrSet[j]=true))->canReqProgress(j)
  end
end;
*/

invariant "ProgressofActiveReq2"
forall i:NODE do
  ( (!isUndefined(CurPtr)) & (CurPtr=i) & ((CurCmd=ReqE)|((CurCmd=ReqS)&ExGntd)) & isUndefined(AuxLastSharer) ) -> canReqProgress(i)
end;

invariant "Interactions"
forall i:NODE do
  forall j:NODE do
    ( (!isUndefined(CurPtr)) & (CurPtr=i) & ((CurCmd=ReqE)|((CurCmd=ReqS)&ExGntd)) & (AuxLastSharer=j) ) -> canReqProgress(j)
  end
end;

--|((ShrSet[j]=true)->canReqProgress(j))))
/*
invariant "ProgressOfReq"
forall i : NODE do  
    (((CurPtr=i)&(forall j: NODE do ShrSet[j]=false end)) -> (canReqSProgress(i)|canReqEProgress(i)))
end;


invariant "Interactions"
forall i:NODE do
  forall j: NODE do
    ((((CurPtr = j)&(i!=j))->conflictingReqProgresses(j))|
     ((ShrSet[j] = true)->conflictingReqProgresses(j)))
  end
end;
*/

/*
invariant "ProgressOfReq"
forall i : NODE do  
  (((CurPtr=i)&(forall j: NODE do ShrSet[j]=false end)) -> (canReqProgress(i)))
end;


invariant "Interactions"
forall i:NODE do
  forall j: NODE do
    ((((CurPtr = j)&(i!=j))->canReqProgress(j))|
     ((ShrSet[j] = true)->canReqProgress(j)))
  end
end;
*/


/*invariant "ProgressOfReq"
forall i : NODE do  
  (((CurPtr=i)&(forall j: NODE do ShrSet[j]=false end)) -> (canReqProgress(i)))
end;

invariant "Interactions"
forall i:NODE do
  forall j: NODE do
    ((((CurPtr = j)&(i!=j))|(ShrSet[j] = true))->canReqProgress(j))
  end
end;
*/

/*Trying to show that a reqS or reqE from cache i can progress at all times and if it can not, there exists, for sure, some other request which can progress*/

/*
invariant "ProgressOfReqUnref"
forall i : NODE do 
  isReqSActive(i) -> (canReqSProgress(i)|canReqEProgress(i))
end;
*/

/*
invariant "ProgressOfReq"
(forall j: NODE do ShrSet[j]=false end) -> (canReqSProgress(CurPtr)|canReqEProgress(CurPtr));

invariant "Interactions"
  forall j: NODE do
   ((ShrSet[j] = true)->conflictingReqProgresses(j))
     end;
*/
