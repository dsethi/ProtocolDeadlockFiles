--| Variable declarations
const
  NODE_NUM : 2;
  DATA_NUM : 2;
type
  NODE : scalarset(NODE_NUM);
  absNODE : union { NODE, enum { o } };
  DATA : scalarset(DATA_NUM);
  CACHE_STATE : enum { I, S, E };
  CACHE : record
    State : CACHE_STATE;
    Data : DATA;
  end;
  MSG_CMD : enum { Empty, ReqS, ReqE, Inv, InvAck, GntS, GntE };
  MSG : record
    Cmd : MSG_CMD;
    Data : DATA;
  end;
var
  Cache : array[NODE] of CACHE;
  Chan1 : array[NODE] of MSG;
  Chan2 : array[NODE] of MSG;
  Chan3 : array[NODE] of MSG;
  InvSet : array[NODE] of boolean;
  ShrSet : array[NODE] of boolean;
  ExGntd : boolean;
  AuxLastSharer: absNODE;
  CurCmd : MSG_CMD;
  CurPtr : absNODE;
  MemData : DATA;
  AuxData : DATA;
type
  CTR : 0..1;
var
  Env_o : CTR;
--| Function and procedure declarations
function absproc (a: absNODE) : BOOLEAN;
  begin
    if a = o then
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

--| Rules
ruleset
  d : DATA
do
startstate "Init"
begin
  for i : NODE do
    Chan1[i].Cmd := Empty;
    Chan2[i].Cmd := Empty;
    Chan3[i].Cmd := Empty;
    Cache[i].State := I;
    InvSet[i] := false;
    ShrSet[i] := false;
  end;
  ExGntd := false;
  CurCmd := Empty;
  MemData := d;
  AuxData := d;
  Env_o := 1;
end;
end;
ruleset
  i : NODE;
  d : DATA
do
rule "Store"
  !isundefined(i) & Cache[i].State = E
==>
begin
  Cache[i].Data := d;
  AuxData := d;
end;
end;
ruleset
  d : DATA
do
rule "absStore"
  Env_o = 1
==>
begin
  AuxData := d;
end;
end;
ruleset
  i : NODE
do
rule "SendReqS"
  !isundefined(i) & Chan1[i].Cmd = Empty & Cache[i].State = I
==>
begin
  Chan1[i].Cmd := ReqS;
end;
end;
ruleset
  i : NODE
do
rule "SendReqE"
  !isundefined(i)
  & Chan1[i].Cmd = Empty
  & (Cache[i].State = I | Cache[i].State = S)
==>
begin
  Chan1[i].Cmd := ReqE;
end;
end;
ruleset
  i : NODE
do
rule "RecvReqS"
  !isundefined(i) & CurCmd = Empty & Chan1[i].Cmd = ReqS
==>
begin
  CurCmd := ReqS;
  CurPtr := i;
  Chan1[i].Cmd := Empty;
  for j : NODE do
    InvSet[j] := ShrSet[j];
  end;
end;
end;
rule "absRecvReqS"
  Env_o = 1 & CurCmd = Empty
==>
begin
  CurCmd := ReqS;
  CurPtr := o;
  for j : NODE do
    InvSet[j] := ShrSet[j];
  end;
end;
ruleset
  i : NODE
do
rule "RecvReqE"
  !isundefined(i) & CurCmd = Empty & Chan1[i].Cmd = ReqE
==>
begin
  CurCmd := ReqE;
  CurPtr := i;
  Chan1[i].Cmd := Empty;
  for j : NODE do
    InvSet[j] := ShrSet[j];
  end;
end;
end;
rule "absRecvReqE"
  Env_o = 1 & CurCmd = Empty
==>
begin
  CurCmd := ReqE;
  CurPtr := o;
  for j : NODE do
    InvSet[j] := ShrSet[j];
  end;
end;
ruleset
  i : NODE
do
rule "SendInv"
  !isundefined(i)
  & Chan2[i].Cmd = Empty
  & InvSet[i] = true
  & (CurCmd = ReqE | CurCmd = ReqS & ExGntd = true)
==>
begin
  Chan2[i].Cmd := Inv;
  InvSet[i] := false;
end;
end;
ruleset
  i : NODE
do
rule "SendInvAck"
  !isundefined(i) & Chan2[i].Cmd = Inv & Chan3[i].Cmd = Empty
==>
begin
  Chan2[i].Cmd := Empty;
  Chan3[i].Cmd := InvAck;
  if Cache[i].State = E & true then
    Chan3[i].Data := Cache[i].Data;
  end;
  Cache[i].State := I;
  undefine Cache[i].Data;
end;
end;
ruleset
  i : NODE
do
rule "RecvInvAck"
  !isundefined(i) & Chan3[i].Cmd = InvAck & CurCmd != Empty
==>
begin
  Chan3[i].Cmd := Empty;
  ShrSet[i] := false;

  undefine AuxLastSharer;
  for p : NODE do
    if (p != i & ShrSet[p]) then
      AuxLastSharer := p;
    end;
  end;

  if ExGntd = true & true then
    ExGntd := false;
    MemData := Chan3[i].Data;
    undefine Chan3[i].Data;
  end;
end;
end;
rule "absRecvInvAck"
  Env_o = 1 & CurCmd != Empty
==>
begin

  undefine AuxLastSharer;
  for p : NODE do
    if (ShrSet[p]) then
      AuxLastSharer := p;
    end;
  end;

  if ExGntd = true & true then
    ExGntd := false;
    undefine MemData;
  end;
end;
ruleset
  i : NODE
do
rule "SendGntS"
  !isundefined(i)
  & CurCmd = ReqS
  & CurPtr = i
  & Chan2[i].Cmd = Empty
  & ExGntd = false
==>
begin
  Chan2[i].Cmd := GntS;
  Chan2[i].Data := MemData;
  ShrSet[i] := true;
  CurCmd := Empty;
  AuxLastSharer := i;
  undefine CurPtr;
end;
end;
rule "absSendGntS"
  Env_o = 1 & CurCmd = ReqS & CurPtr = o & ExGntd = false
==>
begin
  CurCmd := Empty;
  undefine CurPtr;
  AuxLastSharer := o;
end;
ruleset
  i : NODE
do
rule "SendGntE"
  !isundefined(i)
  & CurCmd = ReqE
  & CurPtr = i
  & Chan2[i].Cmd = Empty
  & ExGntd = false
  & forall j : NODE do ShrSet[j] = false end
==>
begin
  Chan2[i].Cmd := GntE;
  Chan2[i].Data := MemData;
  ShrSet[i] := true;
  ExGntd := true;
  CurCmd := Empty;
  AuxLastSharer := i;
  undefine CurPtr;
end;
end;
rule "absSendGntE"
  Env_o = 1
  & CurCmd = ReqE
  & CurPtr = o
  & ExGntd = false
  & forall j : NODE do ShrSet[j] = false end
==>
begin
  ExGntd := true;
  CurCmd := Empty;
  AuxLastSharer := o;
  undefine CurPtr;
end;
ruleset
  i : NODE
do
rule "RecvGntS"
  !isundefined(i) & Chan2[i].Cmd = GntS
==>
begin
  Cache[i].State := S;
  Cache[i].Data := Chan2[i].Data;
  Chan2[i].Cmd := Empty;
  undefine Chan2[i].Data;
end;
end;
ruleset
  i : NODE
do
rule "RecvGntE"
  !isundefined(i) & Chan2[i].Cmd = GntE
==>
begin
  Cache[i].State := E;
  Cache[i].Data := Chan2[i].Data;
  Chan2[i].Cmd := Empty;
  undefine Chan2[i].Data;
end;
end;

invariant "CntrlProp"
  forall i : NODE do
    forall j : NODE do
      i != j ->
        (Cache[i].State = E -> Cache[j].State = I)
        & (Cache[i].State = S -> Cache[j].State = I | Cache[j].State = S)
    end
  end;
invariant "DataProp"
  (ExGntd = false -> MemData = AuxData)
  & forall i : NODE do Cache[i].State != I -> Cache[i].Data = AuxData end;


invariant "ProgressOfReqInit"
forall i : NODE do  
  ((isUndefined(CurPtr)) -> (canReqProgress(i)))
end;


invariant "ProgressOfActiveReq"
forall i : NODE do  
  (((!isUndefined(CurPtr))&(CurPtr=i)&(!((CurCmd=ReqE)|((CurCmd=ReqS)&ExGntd)))) -> (canReqProgress(i)))
end;

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

--| End of model
