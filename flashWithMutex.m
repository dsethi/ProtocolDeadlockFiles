
const

  NODE_NUM : 3;
  DATA_NUM : 2;

type

  NODE : scalarset(NODE_NUM);
  DATA : scalarset(DATA_NUM);

  ABS_NODE : union {NODE, enum{Other}};

  CACHE_STATE : enum {CACHE_I, CACHE_S, CACHE_E};

  NODE_CMD : enum {NODE_None, NODE_Get, NODE_GetX};

  NODE_STATE : record
    ProcCmd : NODE_CMD;
    InvMarked : boolean;
    CacheState : CACHE_STATE;
    CacheData : DATA;
  end;

  DIR_STATE : record
    Pending : boolean;
    Local : boolean;
    Dirty : boolean;
    HeadVld : boolean;
    HeadPtr : ABS_NODE;
    ShrVld : boolean;
    ShrSet : array [NODE] of boolean;
    InvSet : array [NODE] of boolean;
  end;

  UNI_CMD : enum {UNI_None, UNI_Get, UNI_GetX, UNI_Put, UNI_PutX, UNI_Nak};

  UNI_MSG : record
    Cmd : UNI_CMD;
    Proc : ABS_NODE;
    Data : DATA;
  end;

  INV_CMD : enum {INV_None, INV_Inv, INV_InvAck};

  INV_MSG : record
    Cmd : INV_CMD;
  end;

  RP_CMD : enum {RP_None, RP_Replace};

  RP_MSG : record
    Cmd : RP_CMD;
  end;

  WB_CMD : enum {WB_None, WB_Wb};

  WB_MSG : record
    Cmd : WB_CMD;
    Proc : ABS_NODE;
    Data : DATA;
  end;

  SHWB_CMD : enum {SHWB_None, SHWB_ShWb, SHWB_FAck};

  SHWB_MSG : record
    Cmd : SHWB_CMD;
    Proc : ABS_NODE;
    Data : DATA;
  end;

  NAKC_CMD : enum {NAKC_None, NAKC_Nakc};

  NAKC_MSG : record
    Cmd : NAKC_CMD;
  end;

  STATE : record
  -- Program variables:
    Proc : array [NODE] of NODE_STATE;
    Dir : DIR_STATE;
    MemData : DATA;
    UniMsg : array [NODE] of UNI_MSG;
    InvMsg : array [NODE] of INV_MSG;
    RpMsg : array [NODE] of RP_MSG;
    WbMsg : WB_MSG;
    ShWbMsg : SHWB_MSG;
    NakcMsg : NAKC_MSG;
  -- Auxiliary variables:
    CurrData : DATA;
    PrevData : DATA;
    LastWrVld : boolean;
    LastWrPtr : ABS_NODE;
    PendReqSrc : ABS_NODE;
    PendReqCmd : UNI_CMD;
    Collecting : boolean;
    FwdCmd : UNI_CMD;
    FwdSrc : ABS_NODE;
    LastInvAck : ABS_NODE;
    LastOtherInvAck : ABS_NODE;
    Env_o : Boolean;
  end;

var

  Home : NODE;
  Sta : STATE;

-----------------------------Invariants as functions ------------------------

-----------------------------Guards for Get ------------------------
function guardPI_remote_get(src: NODE): Boolean;
begin
return
  src != Home &
  Sta.Proc[src].ProcCmd = NODE_None &
  Sta.Proc[src].CacheState = CACHE_I;
endFunction;

function guardNI_Local_get_NAK(src: NODE): Boolean;
begin
return
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].Proc = Home &
  Sta.RpMsg[src].Cmd != RP_Replace &
  ( Sta.Dir.Pending |
    Sta.Dir.Dirty & Sta.Dir.Local & Sta.Proc[Home].CacheState != CACHE_E |
    Sta.Dir.Dirty & !Sta.Dir.Local & Sta.Dir.HeadPtr = src );

endFunction;

function guardNI_Nak(dst: NODE): Boolean;
begin
return 
   Sta.UniMsg[dst].Cmd = UNI_Nak;
endFunction;


function guardNI_Local_get_put(src: NODE): Boolean;
begin
return
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].Proc = Home &
  Sta.RpMsg[src].Cmd != RP_Replace &
  !Sta.Dir.Pending &
  (Sta.Dir.Dirty -> Sta.Dir.Local & Sta.Proc[Home].CacheState = CACHE_E);
endFunction;

function guardNI_remote_put(dst: NODE): Boolean;
begin
return 
  dst != Home &
  Sta.UniMsg[dst].Cmd = UNI_Put;
endFunction;

function guardNI_Local_get_get(src: NODE): Boolean;
begin
return
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].Proc = Home &
  Sta.RpMsg[src].Cmd != RP_Replace &
  !Sta.Dir.Pending & Sta.Dir.Dirty & !Sta.Dir.Local & Sta.Dir.HeadPtr != src;
endFunction;

function guardNI_remote_get_NAK(src: NODE; dst:NODE): Boolean;
begin
return
  src != dst & dst != Home &
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].Proc = dst &
  Sta.Proc[dst].CacheState != CACHE_E;
endFunction;

function guardNI_NAK_Clear(): Boolean;
begin
return 
  Sta.NakcMsg.Cmd = NAKC_Nakc;
endFunction;

function guardNI_remote_get_put(src : NODE; dst : NODE): Boolean;
begin
return 
  src != dst & dst != Home &
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].Proc = dst &
  Sta.Proc[dst].CacheState = CACHE_E
--  !Sta.Proc[src].InvMarked
endFunction;

function guardNI_shwb(): Boolean;
begin
return
  Sta.ShWbMsg.Cmd = SHWB_ShWb;
endFunction;

function guardNI_local_put(): Boolean;
begin
return
  Sta.UniMsg[Home].Cmd = UNI_Put;
endFunction;

function guardPI_local_get_get(): Boolean;
begin
return
  Sta.Proc[Home].ProcCmd = NODE_None &
  Sta.Proc[Home].CacheState = CACHE_I &
  !Sta.Dir.Pending & Sta.Dir.Dirty;
endFunction;

function guardPI_local_get_put(): Boolean;
begin
return
Sta.Proc[Home].ProcCmd = NODE_None &
  Sta.Proc[Home].CacheState = CACHE_I &
  !Sta.Dir.Pending & !Sta.Dir.Dirty;
endFunction;

-----------------------------Guards for GetX ---------------------------------

function guardPI_remote_getX(src: NODE): Boolean;
begin
return
  src != Home &
  Sta.Proc[src].ProcCmd = NODE_None &
  Sta.Proc[src].CacheState = CACHE_I;
endFunction;

function guardNI_local_getX_Nak(src: NODE): Boolean;
begin
return
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  ( Sta.Dir.Pending |
    Sta.Dir.Dirty & Sta.Dir.Local & Sta.Proc[Home].CacheState != CACHE_E |
    Sta.Dir.Dirty & !Sta.Dir.Local & Sta.Dir.HeadPtr = src );
endFunction;

function guardNI_remote_putX(dst: NODE): Boolean;
begin
return 
 dst != Home &
  Sta.UniMsg[dst].Cmd = UNI_PutX &
  Sta.Proc[dst].ProcCmd = NODE_GetX;
endFunction;

function guardNI_local_getX_getX(src: NODE): Boolean;
begin
return
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  !Sta.Dir.Pending & Sta.Dir.Dirty & !Sta.Dir.Local & Sta.Dir.HeadPtr != src;
endFunction;

function guardNI_remote_getX_NAK(src: NODE; dst:NODE): Boolean;
begin
return
  src != dst & dst != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = dst &
  Sta.Proc[dst].CacheState != CACHE_E
endFunction;

--set dst = Sta.UniMsg[src].Proc
function guardNI_remote_getX_putX(src: NODE; dst:NODE): Boolean;
begin
return
 src != dst & dst != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = dst &
  Sta.Proc[dst].CacheState = CACHE_E;
endFunction;

function guardNI_FACK(): Boolean;
begin
return
  Sta.ShWbMsg.Cmd = SHWB_FAck;
endFunction;

function guardPI_local_getx_getx(): Boolean;
begin
return
  Sta.Proc[Home].ProcCmd = NODE_None &
  ( Sta.Proc[Home].CacheState = CACHE_I |
    Sta.Proc[Home].CacheState = CACHE_S ) &
  !Sta.Dir.Pending & Sta.Dir.Dirty;
endFunction;

function guardPI_local_getx_putx(): Boolean;
begin
return
  Sta.Proc[Home].ProcCmd = NODE_None &
  ( Sta.Proc[Home].CacheState = CACHE_I |
    Sta.Proc[Home].CacheState = CACHE_S ) &
  !Sta.Dir.Pending & !Sta.Dir.Dirty;
endFunction;

function guardNI_local_getX_putX(src: NODE): Boolean;
begin
return
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  !Sta.Dir.Pending &
  (Sta.Dir.Dirty -> Sta.Dir.Local & Sta.Proc[Home].CacheState = CACHE_E);
endFunction;

function guardNI_inv(dst: NODE): Boolean;
begin
return
  dst != Home &
  Sta.InvMsg[dst].Cmd = INV_Inv;
endFunction;

function guardNI_invAck(src: NODE): Boolean;
begin
return
  src != Home &
  Sta.InvMsg[src].Cmd = INV_InvAck &
  Sta.Dir.Pending & Sta.Dir.InvSet[src];
endFunction;

-----------------------------Guards for Misc transactions --------------------
function guardPI_remote_replace(src: NODE): Boolean;
begin
return
  src != Home &
  Sta.Proc[src].ProcCmd = NODE_None &
  Sta.Proc[src].CacheState = CACHE_S;
endFunction;

function guardNI_replace(src: NODE): Boolean;
begin
return
  Sta.RpMsg[src].Cmd = RP_Replace;
endFunction;

function guardPI_local_replace(): Boolean;
begin
return
  Sta.Proc[Home].ProcCmd = NODE_None &
  Sta.Proc[Home].CacheState = CACHE_S;
endFunction;

function guardPI_remote_putX(dst: NODE): Boolean;
begin
return
  dst != Home &
  Sta.Proc[dst].ProcCmd = NODE_None &
  Sta.Proc[dst].CacheState = CACHE_E;
endFunction;

function guardNI_wb(): Boolean;
begin
return
  Sta.WbMsg.Cmd = WB_Wb;
endFunction;

function guardPI_local_putX(): Boolean;
begin
return
  Sta.Proc[Home].ProcCmd = NODE_None &
  Sta.Proc[Home].CacheState = CACHE_E
endfunction;

function guardStore(src: NODE): Boolean;
begin
return
  Sta.Proc[src].CacheState = CACHE_E;
endFunction;

function guardNI_Local_PutXAcksDone(): Boolean;
begin
return
  Sta.UniMsg[Home].Cmd = UNI_PutX;
endFunction;

------------------------------------------------------------------------------

--------------------------Progress of get request-----------------------------

function progress_remote_get(src: NODE; dst: NODE): Boolean;
var
fl1: Boolean;
fl2: Boolean;
fl3: Boolean;
fl4: Boolean;
begin
fl1 := guardPI_remote_get(src) | guardNI_Local_get_NAK(src) | guardNI_Nak(src);

fl2 := guardPI_remote_get(src) | guardNI_Local_get_put(src) | guardNI_remote_put(src);


--Hack: set dst = Sta.UniMsg[src].Proc
fl3 := guardPI_remote_get(src) | guardNI_Local_get_get(src) | guardNI_remote_get_NAK(src, dst) | guardNI_NAK_Clear() | guardNI_Nak(src);

fl4 := guardPI_remote_get(src)| guardNI_Local_get_get(src) | guardNI_remote_get_put(src, dst) | guardNI_shwb()| guardNI_remote_put(src);

return fl1|fl2|fl3|fl4;
--return guardPI_remote_get(src);
endFunction;

function progress_local_get(src: NODE; dst: NODE): Boolean;
var
fl5: Boolean;
fl6: Boolean;
flMissing: Boolean;
begin

--HACK: set dst to Sta.UniMsg[src].Proc
fl5 := guardPI_local_get_get() | guardNI_remote_get_put(src, dst) | guardNI_shwb() | guardNI_local_put();

fl6 := guardPI_local_get_get() | guardNI_remote_get_NAK(src, dst) | guardNI_Nak(src) | guardNI_NAK_Clear();

flMissing := guardPI_local_get_put();

return fl5|fl6|flMissing;
endFunction;

--------------------------Progress of getX request----------------------------

function progress_remote_getX(src: NODE; dst: NODE): Boolean;
var
fl1: Boolean;
fl2: Boolean;
fl3: Boolean;
fl4: Boolean;
fl7: Boolean;
begin

fl1 := guardPI_remote_getX(src)|guardNI_local_getX_Nak(src)|guardNI_Nak(src);

fl2 := guardPI_remote_getX(src)|guardNI_local_getX_putX(src)|guardNI_remote_putX(src);


--HACK: set dst to Sta.UniMsg[src].Proc
fl3 := guardPI_remote_getX(src)|guardNI_local_getX_getX(src)|(guardNI_remote_getX_NAK(src, dst))|guardNI_NAK_Clear()|guardNI_Nak(src);

--HACK: set dst to Sta.UniMsg[src].Proc
fl4 := guardPI_remote_getX(src)|guardNI_local_getX_getX(src)|guardNI_remote_getX_putX(src, dst)|guardNI_FACK()|guardNI_remote_putX(src);

fl7 := guardPI_remote_getX(src)|guardNI_local_getX_getX(src)|guardNI_remote_putX(src); --somehow interfaces with invalidates

return fl1|fl2|fl3|fl4|fl7;

endFunction;

function progress_local_getX(src: NODE; dst: NODE): Boolean;
var
fl5: Boolean;
fl6: Boolean;
flMissing: Boolean;
begin

-- HACK: set dst to Sta.UniMsg[src].Proc
fl5 := guardPI_local_getx_getx() | guardNI_remote_getX_NAK(src, dst) | guardNI_Nak(src) | guardNI_NAK_Clear();

--fl6Buggy := guardPI_local_getx_getx() | guardNI_remote_getX_putX(src, dst) | guardNI_FACK()|guardNI_remote_putX(src);
-- HACK: set dst to Sta.UniMsg[src].Proc
fl6 :=  guardPI_local_getx_getx() | guardNI_remote_getX_putX(src, dst) | guardNI_FACK() | guardNI_Local_PutXAcksDone();

flMissing := guardPI_local_getx_putx();

return fl5|fl6|flMissing;
endFunction;

----------------------------------Invalidate----------------------------------
function progress_invalidate(src: NODE): Boolean;
begin
return guardNI_inv(src)|guardNI_invAck(src);
endFunction;

----------------------------------Misc----------------------------------------

function progress_remote_replace(src: NODE): Boolean;
begin
return guardPI_remote_replace(src)|guardNI_replace(src);
endFunction;

function progress_local_replace(): Boolean;
begin
return guardPI_local_replace();
endFunction;

function progress_remote_replaceX(src: NODE): Boolean;
begin
return guardPI_remote_putX(src)|guardNI_wb();
endFunction;

function progress_local_replaceX(): Boolean;
begin
return guardPI_local_putX();
endFunction;

------------------------------------Final Progress---------------------------

function progress_remote(src: NODE; dst: NODE): Boolean;
begin
return progress_remote_get(src, dst)|progress_remote_getX(src, dst)|guardStore(src)| progress_remote_replace(src)| progress_remote_replaceX(src);
endFunction;

function progress_local(src: NODE; dst: NODE): Boolean;
begin
return progress_local_get(src, dst)|progress_local_getX(src, dst)|guardStore(src)|progress_local_replace()|progress_local_replaceX();
endFunction;

function progress(src: NODE; dst:NODE): Boolean;
begin
if src != Home then
  return progress_remote(src, dst);
else
  return progress_local(src, dst);
endif;
endFunction;

------------------------------------------------------------------------------
ruleset h : NODE; d : DATA do
startstate "Init"
  Home := h;
  undefine Sta;
  Sta.MemData := d;
  Sta.Dir.Pending := false;
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := false;
  Sta.Dir.HeadVld := false;
  Sta.Dir.ShrVld := false;
  Sta.WbMsg.Cmd := WB_None;
  Sta.ShWbMsg.Cmd := SHWB_None;
  Sta.NakcMsg.Cmd := NAKC_None;
  for p : NODE do
    Sta.Proc[p].ProcCmd := NODE_None;
    Sta.Proc[p].InvMarked := false;
    Sta.Proc[p].CacheState := CACHE_I;
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
    Sta.UniMsg[p].Cmd := UNI_None;
    Sta.InvMsg[p].Cmd := INV_None;
    Sta.RpMsg[p].Cmd := RP_None;
  end;
  Sta.CurrData := d;
  Sta.PrevData := d;
  Sta.LastWrVld := false;
  Sta.Collecting := false;
  Sta.FwdCmd := UNI_None;
  Sta.Env_o := true;
endstartstate;
endruleset;

-------------------------------------------------------------------------------

ruleset src : NODE; data : DATA do
rule "Store"
  Sta.Proc[src].CacheState = CACHE_E
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.Proc[src].CacheData := data;
  NxtSta.CurrData := data;
  NxtSta.LastWrVld := true;
  NxtSta.LastWrPtr := src;
--
  Sta := NxtSta;
endrule;
endruleset;

ruleset src : NODE do
rule "PI_Remote_Get"
  src != Home &
  Sta.Proc[src].ProcCmd = NODE_None &
  Sta.Proc[src].CacheState = CACHE_I
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.Proc[src].ProcCmd := NODE_Get;
  NxtSta.UniMsg[src].Cmd := UNI_Get;
  NxtSta.UniMsg[src].Proc := Home;
  undefine NxtSta.UniMsg[src].Data;
--
  Sta := NxtSta;
endrule;
endruleset;

rule "PI_Local_Get_Get"
  Sta.Proc[Home].ProcCmd = NODE_None &
  Sta.Proc[Home].CacheState = CACHE_I &
  !Sta.Dir.Pending & Sta.Dir.Dirty
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.Proc[Home].ProcCmd := NODE_Get;
  NxtSta.Dir.Pending := true;
  NxtSta.UniMsg[Home].Cmd := UNI_Get;
  NxtSta.UniMsg[Home].Proc := Sta.Dir.HeadPtr;
  undefine NxtSta.UniMsg[Home].Data;
  if (Sta.Dir.HeadPtr != Home) then
    NxtSta.FwdCmd := UNI_Get;
  end;
  NxtSta.PendReqSrc := Home;
  NxtSta.PendReqCmd := UNI_Get;
  NxtSta.Collecting := false;
--
  Sta := NxtSta;
endrule;

rule "PI_Local_Get_Put"
  Sta.Proc[Home].ProcCmd = NODE_None &
  Sta.Proc[Home].CacheState = CACHE_I &
  !Sta.Dir.Pending & !Sta.Dir.Dirty
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.Dir.Local := true;
  NxtSta.Proc[Home].ProcCmd := NODE_None;
  if (Sta.Proc[Home].InvMarked) then
    NxtSta.Proc[Home].InvMarked := false;
    NxtSta.Proc[Home].CacheState := CACHE_I;
    undefine NxtSta.Proc[Home].CacheData;
  else
    NxtSta.Proc[Home].CacheState := CACHE_S;
    NxtSta.Proc[Home].CacheData := Sta.MemData;
  end;
--
  Sta := NxtSta;
endrule;

ruleset src : NODE do
rule "PI_Remote_GetX"
  src != Home &
  Sta.Proc[src].ProcCmd = NODE_None &
  Sta.Proc[src].CacheState = CACHE_I
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.Proc[src].ProcCmd := NODE_GetX;
  NxtSta.UniMsg[src].Cmd := UNI_GetX;
  NxtSta.UniMsg[src].Proc := Home;
  undefine NxtSta.UniMsg[src].Data;
--
  Sta := NxtSta;
endrule;
endruleset;

rule "PI_Local_GetX_GetX"
  Sta.Proc[Home].ProcCmd = NODE_None &
  ( Sta.Proc[Home].CacheState = CACHE_I |
    Sta.Proc[Home].CacheState = CACHE_S ) &
  !Sta.Dir.Pending & Sta.Dir.Dirty
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.Proc[Home].ProcCmd := NODE_GetX;
  NxtSta.Dir.Pending := true;
  NxtSta.UniMsg[Home].Cmd := UNI_GetX;
  NxtSta.UniMsg[Home].Proc := Sta.Dir.HeadPtr;
  undefine NxtSta.UniMsg[Home].Data;
  if (Sta.Dir.HeadPtr != Home) then
    NxtSta.FwdCmd := UNI_GetX;
  end;
  NxtSta.PendReqSrc := Home;
  NxtSta.PendReqCmd := UNI_GetX;
  NxtSta.Collecting := false;
--
  Sta := NxtSta;
endrule;

rule "PI_Local_GetX_PutX"
  Sta.Proc[Home].ProcCmd = NODE_None &
  ( Sta.Proc[Home].CacheState = CACHE_I |
    Sta.Proc[Home].CacheState = CACHE_S ) &
  !Sta.Dir.Pending & !Sta.Dir.Dirty
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.Dir.Local := true;
  NxtSta.Dir.Dirty := true;
  if (Sta.Dir.HeadVld) then
    NxtSta.Dir.Pending := true;
    NxtSta.PendReqSrc := Home; --ADDED BY DJ -- CONFIRM
    NxtSta.Dir.HeadVld := false;
    undefine NxtSta.Dir.HeadPtr;
    NxtSta.Dir.ShrVld := false;
    for p : NODE do
      NxtSta.Dir.ShrSet[p] := false;
      if ( p != Home &
           ( Sta.Dir.ShrVld & Sta.Dir.ShrSet[p] |
             Sta.Dir.HeadVld & Sta.Dir.HeadPtr = p ) ) then
        NxtSta.Dir.InvSet[p] := true;
        NxtSta.InvMsg[p].Cmd := INV_Inv;
      else
        NxtSta.Dir.InvSet[p] := false;
        NxtSta.InvMsg[p].Cmd := INV_None;
      end;
    end;
    NxtSta.Collecting := true;
    NxtSta.PrevData := Sta.CurrData;
    NxtSta.LastOtherInvAck := Sta.Dir.HeadPtr;
  end;
  NxtSta.Proc[Home].ProcCmd := NODE_None;
  NxtSta.Proc[Home].InvMarked := false;
  NxtSta.Proc[Home].CacheState := CACHE_E;
  NxtSta.Proc[Home].CacheData := Sta.MemData;
--
  Sta := NxtSta;
endrule;

ruleset dst : NODE do
rule "PI_Remote_PutX"
  dst != Home &
  Sta.Proc[dst].ProcCmd = NODE_None &
  Sta.Proc[dst].CacheState = CACHE_E
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.Proc[dst].CacheState := CACHE_I;
  undefine NxtSta.Proc[dst].CacheData;
  NxtSta.WbMsg.Cmd := WB_Wb;
  NxtSta.WbMsg.Proc := dst;
  NxtSta.WbMsg.Data := Sta.Proc[dst].CacheData;
--
  Sta := NxtSta;
endrule;
endruleset;

rule "PI_Local_PutX"
  Sta.Proc[Home].ProcCmd = NODE_None &
  Sta.Proc[Home].CacheState = CACHE_E
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  if (Sta.Dir.Pending) then
    NxtSta.Proc[Home].CacheState := CACHE_I;
    undefine NxtSta.Proc[Home].CacheData;
    NxtSta.Dir.Dirty := false;
    NxtSta.MemData := Sta.Proc[Home].CacheData;
  else
    NxtSta.Proc[Home].CacheState := CACHE_I;
    undefine NxtSta.Proc[Home].CacheData;
    NxtSta.Dir.Local := false;
    NxtSta.Dir.Dirty := false;
    NxtSta.MemData := Sta.Proc[Home].CacheData;
  end;
--
  Sta := NxtSta;
endrule;

ruleset src : NODE do
rule "PI_Remote_Replace"
  src != Home &
  Sta.Proc[src].ProcCmd = NODE_None &
  Sta.Proc[src].CacheState = CACHE_S
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.Proc[src].CacheState := CACHE_I;
  undefine NxtSta.Proc[src].CacheData;
  NxtSta.RpMsg[src].Cmd := RP_Replace;
--
  Sta := NxtSta;
endrule;
endruleset;

rule "PI_Local_Replace"
  Sta.Proc[Home].ProcCmd = NODE_None &
  Sta.Proc[Home].CacheState = CACHE_S
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.Dir.Local := false;
  NxtSta.Proc[Home].CacheState := CACHE_I;
  undefine NxtSta.Proc[Home].CacheData;
--
  Sta := NxtSta;
endrule;

ruleset dst : NODE do
rule "NI_Nak"
  Sta.UniMsg[dst].Cmd = UNI_Nak
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.UniMsg[dst].Cmd := UNI_None;
  undefine NxtSta.UniMsg[dst].Proc;
  undefine NxtSta.UniMsg[dst].Data;
  NxtSta.Proc[dst].ProcCmd := NODE_None;
  NxtSta.Proc[dst].InvMarked := false;
--
  Sta := NxtSta;
endrule;
endruleset;

rule "NI_Nak_Clear"
  Sta.NakcMsg.Cmd = NAKC_Nakc
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.NakcMsg.Cmd := NAKC_None;
  NxtSta.Dir.Pending := false;
--
  Sta := NxtSta;
endrule;

ruleset src : NODE do
rule "NI_Local_Get_Nak"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].Proc = Home &
  Sta.RpMsg[src].Cmd != RP_Replace &
  ( Sta.Dir.Pending |
    Sta.Dir.Dirty & Sta.Dir.Local & Sta.Proc[Home].CacheState != CACHE_E |
    Sta.Dir.Dirty & !Sta.Dir.Local & Sta.Dir.HeadPtr = src )
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.UniMsg[src].Cmd := UNI_Nak;
  NxtSta.UniMsg[src].Proc := Home;
  undefine NxtSta.UniMsg[src].Data;
--
  Sta := NxtSta;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_Get_Get"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].Proc = Home &
  Sta.RpMsg[src].Cmd != RP_Replace &
  !Sta.Dir.Pending & Sta.Dir.Dirty & !Sta.Dir.Local & Sta.Dir.HeadPtr != src
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.Dir.Pending := true;
  NxtSta.UniMsg[src].Cmd := UNI_Get;
  NxtSta.UniMsg[src].Proc := Sta.Dir.HeadPtr;
  undefine NxtSta.UniMsg[src].Data;
  if (Sta.Dir.HeadPtr != Home) then
    NxtSta.FwdCmd := UNI_Get;
  end;
  NxtSta.PendReqSrc := src;
  NxtSta.PendReqCmd := UNI_Get;
  NxtSta.Collecting := false;
--
  Sta := NxtSta;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_Get_Put"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].Proc = Home &
  Sta.RpMsg[src].Cmd != RP_Replace &
  !Sta.Dir.Pending &
  (Sta.Dir.Dirty -> Sta.Dir.Local & Sta.Proc[Home].CacheState = CACHE_E)
--  !Sta.Proc[src].InvMarked
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  if (Sta.Dir.Dirty) then
    NxtSta.Dir.Dirty := false;
    NxtSta.Dir.HeadVld := true;
    NxtSta.Dir.HeadPtr := src;
    NxtSta.MemData := Sta.Proc[Home].CacheData;
    NxtSta.Proc[Home].CacheState := CACHE_S;
    NxtSta.UniMsg[src].Cmd := UNI_Put;
    NxtSta.UniMsg[src].Proc := Home;
    NxtSta.UniMsg[src].Data := Sta.Proc[Home].CacheData;
  else
    if (Sta.Dir.HeadVld) then
      NxtSta.Dir.ShrVld := true;
      NxtSta.Dir.ShrSet[src] := true;
      for p : NODE do
        NxtSta.Dir.InvSet[p] := (p = src) | Sta.Dir.ShrSet[p];
      end;
    else
      NxtSta.Dir.HeadVld := true;
      NxtSta.Dir.HeadPtr := src;
    end;
    NxtSta.UniMsg[src].Cmd := UNI_Put;
    NxtSta.UniMsg[src].Proc := Home;
    NxtSta.UniMsg[src].Data := Sta.MemData;
  end;
--
  Sta := NxtSta;
endrule;
endruleset;

ruleset src : NODE; dst : NODE do
rule "NI_Remote_Get_Nak"
  src != dst & dst != Home &
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].Proc = dst &
  Sta.Proc[dst].CacheState != CACHE_E
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.UniMsg[src].Cmd := UNI_Nak;
  NxtSta.UniMsg[src].Proc := dst;
  undefine NxtSta.UniMsg[src].Data;
  NxtSta.NakcMsg.Cmd := NAKC_Nakc;
  NxtSta.FwdCmd := UNI_None;
  NxtSta.FwdSrc := src;
--
  Sta := NxtSta;
endrule;
endruleset;

ruleset src : NODE; dst : NODE do
rule "NI_Remote_Get_Put"
  src != dst & dst != Home &
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].Proc = dst &
  Sta.Proc[dst].CacheState = CACHE_E
--  !Sta.Proc[src].InvMarked
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.Proc[dst].CacheState := CACHE_S;
  NxtSta.UniMsg[src].Cmd := UNI_Put;
  NxtSta.UniMsg[src].Proc := dst;
  NxtSta.UniMsg[src].Data := Sta.Proc[dst].CacheData;
  if (src != Home) then
    NxtSta.ShWbMsg.Cmd := SHWB_ShWb;
    NxtSta.ShWbMsg.Proc := src;
    NxtSta.ShWbMsg.Data := Sta.Proc[dst].CacheData;
  end;
  NxtSta.FwdCmd := UNI_None;
  NxtSta.FwdSrc := src;
--
  Sta := NxtSta;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_GetX_Nak"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  ( Sta.Dir.Pending |
    Sta.Dir.Dirty & Sta.Dir.Local & Sta.Proc[Home].CacheState != CACHE_E |
    Sta.Dir.Dirty & !Sta.Dir.Local & Sta.Dir.HeadPtr = src )
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.UniMsg[src].Cmd := UNI_Nak;
  NxtSta.UniMsg[src].Proc := Home;
  undefine NxtSta.UniMsg[src].Data;
--
  Sta := NxtSta;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_GetX_GetX"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  !Sta.Dir.Pending & Sta.Dir.Dirty & !Sta.Dir.Local & Sta.Dir.HeadPtr != src
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.Dir.Pending := true;
  NxtSta.UniMsg[src].Cmd := UNI_GetX;
  NxtSta.UniMsg[src].Proc := Sta.Dir.HeadPtr;
  undefine NxtSta.UniMsg[src].Data;
  if (Sta.Dir.HeadPtr != Home) then
    NxtSta.FwdCmd := UNI_GetX;
  end;
  NxtSta.PendReqSrc := src;
  NxtSta.PendReqCmd := UNI_GetX;
  NxtSta.Collecting := false;
--
  Sta := NxtSta;
endrule;
endruleset;

ruleset src : NODE do
rule "NI_Local_GetX_PutX"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  !Sta.Dir.Pending &
  (Sta.Dir.Dirty -> Sta.Dir.Local & Sta.Proc[Home].CacheState = CACHE_E)
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  if (Sta.Dir.Dirty) then
    NxtSta.Dir.Local := false;
    NxtSta.Dir.Dirty := true;
    NxtSta.Dir.HeadVld := true;
    NxtSta.Dir.HeadPtr := src;
    NxtSta.Dir.ShrVld := false;
    for p : NODE do
      NxtSta.Dir.ShrSet[p] := false;
      NxtSta.Dir.InvSet[p] := false;
    end;
    NxtSta.UniMsg[src].Cmd := UNI_PutX;
    NxtSta.UniMsg[src].Proc := Home;
    NxtSta.UniMsg[src].Data := Sta.Proc[Home].CacheData;
    NxtSta.Proc[Home].CacheState := CACHE_I;
    undefine NxtSta.Proc[Home].CacheData;
  elsif (Sta.Dir.HeadVld ->
         Sta.Dir.HeadPtr = src  &
         forall p : NODE do p != src -> !Sta.Dir.ShrSet[p] end) then
    NxtSta.Dir.Local := false;
    NxtSta.Dir.Dirty := true;
    NxtSta.Dir.HeadVld := true;
    NxtSta.Dir.HeadPtr := src;
    NxtSta.Dir.ShrVld := false;
    for p : NODE do
      NxtSta.Dir.ShrSet[p] := false;
      NxtSta.Dir.InvSet[p] := false;
    end;
    NxtSta.UniMsg[src].Cmd := UNI_PutX;
    NxtSta.UniMsg[src].Proc := Home;
    NxtSta.UniMsg[src].Data := Sta.MemData;
    NxtSta.Proc[Home].CacheState := CACHE_I;
    undefine NxtSta.Proc[Home].CacheData;
    if (Sta.Dir.Local) then
      NxtSta.Proc[Home].CacheState := CACHE_I;
      undefine NxtSta.Proc[Home].CacheData;
      if (Sta.Proc[Home].ProcCmd = NODE_Get) then
        NxtSta.Proc[Home].InvMarked := true;
      end;
    end;
  else
    NxtSta.Dir.Pending := true;
    NxtSta.Dir.Local := false;
    NxtSta.Dir.Dirty := true;
    NxtSta.Dir.HeadVld := true;
    NxtSta.Dir.HeadPtr := src;
    NxtSta.Dir.ShrVld := false;
    for p : NODE do
      NxtSta.Dir.ShrSet[p] := false;
      if ( p != Home & p != src &
           ( Sta.Dir.ShrVld & Sta.Dir.ShrSet[p] |
             Sta.Dir.HeadVld & Sta.Dir.HeadPtr = p ) ) then
        NxtSta.Dir.InvSet[p] := true;
        NxtSta.InvMsg[p].Cmd := INV_Inv;
      else
        NxtSta.Dir.InvSet[p] := false;
        NxtSta.InvMsg[p].Cmd := INV_None;
      end;
    end;
    NxtSta.UniMsg[src].Cmd := UNI_PutX;
    NxtSta.UniMsg[src].Proc := Home;
    NxtSta.UniMsg[src].Data := Sta.MemData;
    if (Sta.Dir.Local) then
      NxtSta.Proc[Home].CacheState := CACHE_I;
      undefine NxtSta.Proc[Home].CacheData;
      if (Sta.Proc[Home].ProcCmd = NODE_Get) then
        NxtSta.Proc[Home].InvMarked := true;
      end;
    end;
    NxtSta.PendReqSrc := src;
    NxtSta.PendReqCmd := UNI_GetX;
    NxtSta.Collecting := true;
    NxtSta.PrevData := Sta.CurrData;
    if (Sta.Dir.HeadPtr != src) then
      NxtSta.LastOtherInvAck := Sta.Dir.HeadPtr;
    else
      for p : NODE do
        if (p != src & Sta.Dir.ShrSet[p]) then NxtSta.LastOtherInvAck := p end;
      end;
    end;
  end;
--
  Sta := NxtSta;
endrule;
endruleset;

ruleset src : NODE; dst : NODE do
rule "NI_Remote_GetX_Nak"
  src != dst & dst != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = dst &
  Sta.Proc[dst].CacheState != CACHE_E
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.UniMsg[src].Cmd := UNI_Nak;
  NxtSta.UniMsg[src].Proc := dst;
  undefine NxtSta.UniMsg[src].Data;
  NxtSta.NakcMsg.Cmd := NAKC_Nakc;
  NxtSta.FwdCmd := UNI_None;
  NxtSta.FwdSrc := src;
--
  Sta := NxtSta;
endrule;
endruleset;

ruleset src : NODE; dst : NODE do
rule "NI_Remote_GetX_PutX"
  src != dst & dst != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = dst &
  Sta.Proc[dst].CacheState = CACHE_E
--  !Sta.Proc[src].InvMarked
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.Proc[dst].CacheState := CACHE_I;
  undefine NxtSta.Proc[dst].CacheData;
  NxtSta.UniMsg[src].Cmd := UNI_PutX;
  NxtSta.UniMsg[src].Proc := dst;
  NxtSta.UniMsg[src].Data := Sta.Proc[dst].CacheData;
  if (src != Home) then
    NxtSta.ShWbMsg.Cmd := SHWB_FAck;
    NxtSta.ShWbMsg.Proc := src;
    undefine NxtSta.ShWbMsg.Data;
  end;
  NxtSta.FwdCmd := UNI_None;
  NxtSta.FwdSrc := src;
--
  Sta := NxtSta;
endrule;
endruleset;

rule "NI_Local_Put"
  Sta.UniMsg[Home].Cmd = UNI_Put
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.UniMsg[Home].Cmd := UNI_None;
  undefine NxtSta.UniMsg[Home].Proc;
  undefine NxtSta.UniMsg[Home].Data;
  NxtSta.Dir.Pending := false;
  NxtSta.Dir.Dirty := false;
  NxtSta.Dir.Local := true;
  NxtSta.MemData := Sta.UniMsg[Home].Data;
  NxtSta.Proc[Home].ProcCmd := NODE_None;
  if (Sta.Proc[Home].InvMarked) then
    NxtSta.Proc[Home].InvMarked := false;
    NxtSta.Proc[Home].CacheState := CACHE_I;
    undefine NxtSta.Proc[Home].CacheData;
  else
    NxtSta.Proc[Home].CacheState := CACHE_S;
    NxtSta.Proc[Home].CacheData := Sta.UniMsg[Home].Data;
  end;
--
  Sta := NxtSta;
endrule;

ruleset dst : NODE do
rule "NI_Remote_Put"
  dst != Home &
  Sta.UniMsg[dst].Cmd = UNI_Put
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.UniMsg[dst].Cmd := UNI_None;
  undefine NxtSta.UniMsg[dst].Proc;
  undefine NxtSta.UniMsg[dst].Data;
  NxtSta.Proc[dst].ProcCmd := NODE_None;
  if (Sta.Proc[dst].InvMarked) then
    NxtSta.Proc[dst].InvMarked := false;
    NxtSta.Proc[dst].CacheState := CACHE_I;
    undefine NxtSta.Proc[dst].CacheData;
  else
    NxtSta.Proc[dst].CacheState := CACHE_S;
    NxtSta.Proc[dst].CacheData := Sta.UniMsg[dst].Data;
  end;
--
  Sta := NxtSta;
endrule;
endruleset;

rule "NI_Local_PutXAcksDone"
  Sta.UniMsg[Home].Cmd = UNI_PutX
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.UniMsg[Home].Cmd := UNI_None;
  undefine NxtSta.UniMsg[Home].Proc;
  undefine NxtSta.UniMsg[Home].Data;
  NxtSta.Dir.Pending := false;
  NxtSta.Dir.Local := true;
  NxtSta.Dir.HeadVld := false;
  undefine NxtSta.Dir.HeadPtr;
  NxtSta.Proc[Home].ProcCmd := NODE_None;
  NxtSta.Proc[Home].InvMarked := false;
  NxtSta.Proc[Home].CacheState := CACHE_E;
  NxtSta.Proc[Home].CacheData := Sta.UniMsg[Home].Data;
--
  Sta := NxtSta;
endrule;

ruleset dst : NODE do
rule "NI_Remote_PutX"
  dst != Home &
  Sta.UniMsg[dst].Cmd = UNI_PutX &
  Sta.Proc[dst].ProcCmd = NODE_GetX
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.UniMsg[dst].Cmd := UNI_None;
  undefine NxtSta.UniMsg[dst].Proc;
  undefine NxtSta.UniMsg[dst].Data;
  NxtSta.Proc[dst].ProcCmd := NODE_None;
  NxtSta.Proc[dst].InvMarked := false;
  NxtSta.Proc[dst].CacheState := CACHE_E;
  NxtSta.Proc[dst].CacheData := Sta.UniMsg[dst].Data;
--
  Sta := NxtSta;
endrule;
endruleset;

ruleset dst : NODE do
rule "NI_Inv"
  dst != Home &
  Sta.InvMsg[dst].Cmd = INV_Inv
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.InvMsg[dst].Cmd := INV_InvAck;
  NxtSta.Proc[dst].CacheState := CACHE_I;
  undefine NxtSta.Proc[dst].CacheData;
  if (Sta.Proc[dst].ProcCmd = NODE_Get) then
    NxtSta.Proc[dst].InvMarked := true;
  end;
--
  Sta := NxtSta;
endrule;
endruleset;

---- This rule is wrong!! Collecting is set to false once invacks are received from concrete procs
---- Thus invacks from "Other" are thrown away! Could have been caught by some kind of syntax checker....

ruleset src : NODE do
rule "NI_InvAck"
  src != Home &
  Sta.InvMsg[src].Cmd = INV_InvAck &
  Sta.Dir.Pending & Sta.Dir.InvSet[src]  
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.InvMsg[src].Cmd := INV_None;
  NxtSta.Dir.InvSet[src] := false;
  if (exists p : NODE do p != src & Sta.Dir.InvSet[p] end) then
    NxtSta.LastInvAck := src;
    for p : NODE do
      if (p != src & Sta.Dir.InvSet[p]) then
        NxtSta.LastOtherInvAck := p;
      end;
    end;
  else
    NxtSta.Dir.Pending := false;
    if (Sta.Dir.Local & !Sta.Dir.Dirty) then
      NxtSta.Dir.Local := false;
    end;
    NxtSta.Collecting := false;
    NxtSta.LastInvAck := src;
  end;
--
  Sta := NxtSta;
endrule;
endruleset;

rule "NI_Wb"
  Sta.WbMsg.Cmd = WB_Wb
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.WbMsg.Cmd := WB_None;
  undefine NxtSta.WbMsg.Proc;
  undefine NxtSta.WbMsg.Data;
  NxtSta.Dir.Dirty := false;
  NxtSta.Dir.HeadVld := false;
  undefine NxtSta.Dir.HeadPtr;
  NxtSta.MemData := Sta.WbMsg.Data;
--
  Sta := NxtSta;
endrule;

rule "NI_FAck"
  Sta.ShWbMsg.Cmd = SHWB_FAck
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.ShWbMsg.Cmd := SHWB_None;
  undefine NxtSta.ShWbMsg.Proc;
  undefine NxtSta.ShWbMsg.Data;
  NxtSta.Dir.Pending := false;
  if (Sta.Dir.Dirty) then
    NxtSta.Dir.HeadPtr := Sta.ShWbMsg.Proc;
  end;
--
  Sta := NxtSta;
endrule;

rule "NI_ShWb"
  Sta.ShWbMsg.Cmd = SHWB_ShWb
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.ShWbMsg.Cmd := SHWB_None;
  undefine NxtSta.ShWbMsg.Proc;
  undefine NxtSta.ShWbMsg.Data;
  NxtSta.Dir.Pending := false;
  NxtSta.Dir.Dirty := false;
  NxtSta.Dir.ShrVld := true;
--  NxtSta.Dir.ShrSet[Sta.ShWbMsg.Proc] := true;
  for p : NODE do
    NxtSta.Dir.ShrSet[p] := (p = Sta.ShWbMsg.Proc) | Sta.Dir.ShrSet[p];
    NxtSta.Dir.InvSet[p] := (p = Sta.ShWbMsg.Proc) | Sta.Dir.ShrSet[p];
  end;
  NxtSta.MemData := Sta.ShWbMsg.Data;
--
  Sta := NxtSta;
endrule;

ruleset src : NODE do
rule "NI_Replace"
  Sta.RpMsg[src].Cmd = RP_Replace
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.RpMsg[src].Cmd := RP_None;
  if (Sta.Dir.ShrVld) then
    NxtSta.Dir.ShrSet[src] := false;
    NxtSta.Dir.InvSet[src] := false;
  end;
--
  Sta := NxtSta;
endrule;
endruleset;

-------------------------------------------------------------------------------


invariant "CacheStateProp"
  forall p : NODE do forall q : NODE do
    p != q ->
    !(Sta.Proc[p].CacheState = CACHE_E & Sta.Proc[q].CacheState = CACHE_E)
  end end;

invariant "CacheDataProp"
  forall p : NODE do
    ( Sta.Proc[p].CacheState = CACHE_E ->
      Sta.Proc[p].CacheData = Sta.CurrData ) &
    ( Sta.Proc[p].CacheState = CACHE_S ->
      ( Sta.Collecting -> Sta.Proc[p].CacheData = Sta.PrevData ) &
      (!Sta.Collecting -> Sta.Proc[p].CacheData = Sta.CurrData ) )
  end;

invariant "MemDataProp"
  !Sta.Dir.Dirty -> Sta.MemData = Sta.CurrData;

-------------------------------------------------------------------------------

rule "ABS_Other"
Sta.Env_o & true
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
--
  Sta := NxtSta;
endrule;

ruleset data : DATA do
rule "ABS_Store"
Sta.Env_o & Sta.Dir.Dirty & Sta.WbMsg.Cmd != WB_Wb & Sta.ShWbMsg.Cmd != SHWB_ShWb &
  forall p : NODE do Sta.Proc[p].CacheState != CACHE_E end &
  Sta.UniMsg[Home].Cmd != UNI_Put &
  forall q : NODE do Sta.UniMsg[q].Cmd != UNI_PutX end  -- by Lemma_1
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.CurrData := data;
  NxtSta.LastWrVld := true;
  NxtSta.LastWrPtr := Other;
--
  Sta := NxtSta;
endrule;
endruleset;

rule "ABS_PI_Remote_PutX"
Sta.Env_o & Sta.Dir.Dirty & Sta.WbMsg.Cmd != WB_Wb & Sta.ShWbMsg.Cmd != SHWB_ShWb &
  forall p : NODE do Sta.Proc[p].CacheState != CACHE_E end &
  Sta.UniMsg[Home].Cmd != UNI_Put &
  forall q : NODE do Sta.UniMsg[q].Cmd != UNI_PutX end  -- by Lemma_1
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.WbMsg.Cmd := WB_Wb;
  NxtSta.WbMsg.Proc := Other;
  NxtSta.WbMsg.Data := Sta.CurrData;  -- by Lemma_5
--
  Sta := NxtSta;
endrule;

rule "ABS_NI_Local_Get_Get"
Sta.Env_o & !Sta.Dir.Pending & Sta.Dir.Dirty & !Sta.Dir.Local & Sta.Dir.HeadPtr != Other
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.Dir.Pending := true;
  if (Sta.Dir.HeadPtr != Home) then
    NxtSta.FwdCmd := UNI_Get;
  end;
  NxtSta.PendReqSrc := Other;
  NxtSta.PendReqCmd := UNI_Get;
  NxtSta.Collecting := false;
--
  Sta := NxtSta;
endrule;

rule "ABS_NI_Local_Get_Put"
Sta.Env_o & !Sta.Dir.Pending &
  (Sta.Dir.Dirty -> Sta.Dir.Local & Sta.Proc[Home].CacheState = CACHE_E)
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  if (Sta.Dir.Dirty) then
    NxtSta.Dir.Dirty := false;
    NxtSta.Dir.HeadVld := true;
    NxtSta.Dir.HeadPtr := Other;
    NxtSta.MemData := Sta.Proc[Home].CacheData;
    NxtSta.Proc[Home].CacheState := CACHE_S;
  else
    if (Sta.Dir.HeadVld) then
      NxtSta.Dir.ShrVld := true;
      for p : NODE do
        NxtSta.Dir.InvSet[p] := Sta.Dir.ShrSet[p];
      end;
    else
      NxtSta.Dir.HeadVld := true;
      NxtSta.Dir.HeadPtr := Other;
    end;
  end;
--
  Sta := NxtSta;
endrule;

ruleset dst : NODE do
rule "ABS_NI_Remote_Get_Nak_src"
Sta.Env_o & dst != Home &
  Sta.Proc[dst].CacheState != CACHE_E &
  Sta.Dir.Pending & !Sta.Dir.Local &
  Sta.PendReqSrc = Other & Sta.FwdCmd = UNI_Get  -- by Lemma_2
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.NakcMsg.Cmd := NAKC_Nakc;
  NxtSta.FwdCmd := UNI_None;
  NxtSta.FwdSrc := Other;
--
  Sta := NxtSta;
endrule;
endruleset;

ruleset src : NODE do
rule "ABS_NI_Remote_Get_Nak_dst"
Sta.Env_o & Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].Proc = Other &
  Sta.Dir.Pending & !Sta.Dir.Local &
  Sta.PendReqSrc = src & Sta.FwdCmd = UNI_Get  -- by Lemma_2
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.UniMsg[src].Cmd := UNI_Nak;
  NxtSta.UniMsg[src].Proc := Other;
  undefine NxtSta.UniMsg[src].Data;
  NxtSta.NakcMsg.Cmd := NAKC_Nakc;
  NxtSta.FwdCmd := UNI_None;
  NxtSta.FwdSrc := src;
--
  Sta := NxtSta;
endrule;
endruleset;

rule "ABS_NI_Remote_Get_Nak_src_dst"
Sta.Env_o & Sta.Dir.Pending & !Sta.Dir.Local &
  Sta.PendReqSrc = Other & Sta.FwdCmd = UNI_Get  -- by Lemma_2
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.NakcMsg.Cmd := NAKC_Nakc;
  NxtSta.FwdCmd := UNI_None;
  NxtSta.FwdSrc := Other;
--
  Sta := NxtSta;
endrule;

ruleset dst : NODE do
rule "ABS_NI_Remote_Get_Put_src"
Sta.Env_o & dst != Home &
  Sta.Proc[dst].CacheState = CACHE_E &
  Sta.Dir.Pending & !Sta.Dir.Local &
  Sta.PendReqSrc = Other & Sta.FwdCmd = UNI_Get  -- by Lemma_2
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.Proc[dst].CacheState := CACHE_S;
  NxtSta.ShWbMsg.Cmd := SHWB_ShWb;
  NxtSta.ShWbMsg.Proc := Other;
  NxtSta.ShWbMsg.Data := Sta.Proc[dst].CacheData;
  NxtSta.FwdCmd := UNI_None;
  NxtSta.FwdSrc := Other;
--
  Sta := NxtSta;
endrule;
endruleset;

ruleset src : NODE do
rule "ABS_NI_Remote_Get_Put_dst"
Sta.Env_o & Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].Proc = Other &
  Sta.Dir.Dirty & Sta.WbMsg.Cmd != WB_Wb & Sta.ShWbMsg.Cmd != SHWB_ShWb &
  forall p : NODE do Sta.Proc[p].CacheState != CACHE_E end &
  Sta.UniMsg[Home].Cmd != UNI_Put &
  forall q : NODE do Sta.UniMsg[q].Cmd != UNI_PutX end &  -- by Lemma_1
  Sta.Dir.Pending & !Sta.Dir.Local &
  Sta.PendReqSrc = src & Sta.FwdCmd = UNI_Get  -- by Lemma_2
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.UniMsg[src].Cmd := UNI_Put;
  NxtSta.UniMsg[src].Proc := Other;
  NxtSta.UniMsg[src].Data := Sta.CurrData;  -- by Lemma_5
  if (src != Home) then
    NxtSta.ShWbMsg.Cmd := SHWB_ShWb;
    NxtSta.ShWbMsg.Proc := src;
    NxtSta.ShWbMsg.Data := Sta.CurrData;  -- by Lemma_5
  end;
  NxtSta.FwdCmd := UNI_None;
  NxtSta.FwdSrc := src;
--
  Sta := NxtSta;
endrule;
endruleset;

rule "ABS_NI_Remote_Get_Put_src_dst"
Sta.Env_o & Sta.Dir.Dirty & Sta.WbMsg.Cmd != WB_Wb & Sta.ShWbMsg.Cmd != SHWB_ShWb &
  forall p : NODE do Sta.Proc[p].CacheState != CACHE_E end &
  Sta.UniMsg[Home].Cmd != UNI_Put &
  forall q : NODE do Sta.UniMsg[q].Cmd != UNI_PutX end &  -- by Lemma_1
  Sta.Dir.Pending & !Sta.Dir.Local &
  Sta.PendReqSrc = Other & Sta.FwdCmd = UNI_Get  -- by Lemma_2
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.ShWbMsg.Cmd := SHWB_ShWb;
  NxtSta.ShWbMsg.Proc := Other;
  NxtSta.ShWbMsg.Data := Sta.CurrData;  -- by Lemma_5;
  NxtSta.FwdCmd := UNI_None;
  NxtSta.FwdSrc := Other;
--
  Sta := NxtSta;
endrule;

rule "ABS_NI_Local_GetX_GetX"
Sta.Env_o & !Sta.Dir.Pending & Sta.Dir.Dirty & !Sta.Dir.Local & Sta.Dir.HeadPtr != Other
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.Dir.Pending := true;
  if (Sta.Dir.HeadPtr != Home) then
    NxtSta.FwdCmd := UNI_GetX;
  end;
  NxtSta.PendReqSrc := Other;
  NxtSta.PendReqCmd := UNI_GetX;
  NxtSta.Collecting := false;
--
  Sta := NxtSta;
endrule;

rule "ABS_NI_Local_GetX_PutX"
Sta.Env_o & !Sta.Dir.Pending &
  (Sta.Dir.Dirty -> Sta.Dir.Local & Sta.Proc[Home].CacheState = CACHE_E)
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  if (Sta.Dir.Dirty) then
    NxtSta.Dir.Local := false;
    NxtSta.Dir.Dirty := true;
    NxtSta.Dir.HeadVld := true;
    NxtSta.Dir.HeadPtr := Other;
    NxtSta.Dir.ShrVld := false;
    for p : NODE do
      NxtSta.Dir.ShrSet[p] := false;
      NxtSta.Dir.InvSet[p] := false;
    end;
    NxtSta.Proc[Home].CacheState := CACHE_I;
    undefine NxtSta.Proc[Home].CacheData;
  elsif (Sta.Dir.HeadVld ->
         Sta.Dir.HeadPtr = Other  &
         forall p : NODE do !Sta.Dir.ShrSet[p] end) then
    NxtSta.Dir.Local := false;
    NxtSta.Dir.Dirty := true;
    NxtSta.Dir.HeadVld := true;
    NxtSta.Dir.HeadPtr := Other;
    NxtSta.Dir.ShrVld := false;
    for p : NODE do
      NxtSta.Dir.ShrSet[p] := false;
      NxtSta.Dir.InvSet[p] := false;
    end;
    NxtSta.Proc[Home].CacheState := CACHE_I;
    undefine NxtSta.Proc[Home].CacheData;
    if (Sta.Dir.Local) then
      NxtSta.Proc[Home].CacheState := CACHE_I;
      undefine NxtSta.Proc[Home].CacheData;
      if (Sta.Proc[Home].ProcCmd = NODE_Get) then
        NxtSta.Proc[Home].InvMarked := true;
      end;
    end;
  else
    NxtSta.Dir.Pending := true;
    NxtSta.Dir.Local := false;
    NxtSta.Dir.Dirty := true;
    NxtSta.Dir.HeadVld := true;
    NxtSta.Dir.HeadPtr := Other;
    NxtSta.Dir.ShrVld := false;
    for p : NODE do
      NxtSta.Dir.ShrSet[p] := false;
      if ( p != Home &
           ( Sta.Dir.ShrVld & Sta.Dir.ShrSet[p] |
             Sta.Dir.HeadVld & Sta.Dir.HeadPtr = p ) ) then
        NxtSta.Dir.InvSet[p] := true;
        NxtSta.InvMsg[p].Cmd := INV_Inv;
      else
        NxtSta.Dir.InvSet[p] := false;
        NxtSta.InvMsg[p].Cmd := INV_None;
      end;
    end;
    if (Sta.Dir.Local) then
      NxtSta.Proc[Home].CacheState := CACHE_I;
      undefine NxtSta.Proc[Home].CacheData;
      if (Sta.Proc[Home].ProcCmd = NODE_Get) then
        NxtSta.Proc[Home].InvMarked := true;
      end;
    end;
    NxtSta.PendReqSrc := Other;
    NxtSta.PendReqCmd := UNI_GetX;
    NxtSta.Collecting := true;
    NxtSta.PrevData := Sta.CurrData;
    if (Sta.Dir.HeadPtr != Other) then
      NxtSta.LastOtherInvAck := Sta.Dir.HeadPtr;
    else
      for p : NODE do
        if (Sta.Dir.ShrSet[p]) then NxtSta.LastOtherInvAck := p end;
      end;
    end;
  end;
--
  Sta := NxtSta;
endrule;

ruleset dst : NODE do
rule "ABS_NI_Remote_GetX_Nak_src"
Sta.Env_o & dst != Home &
  Sta.Proc[dst].CacheState != CACHE_E &
  Sta.Dir.Pending & !Sta.Dir.Local &
  Sta.PendReqSrc = Other & Sta.FwdCmd = UNI_GetX  -- by Lemma_3
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.NakcMsg.Cmd := NAKC_Nakc;
  NxtSta.FwdCmd := UNI_None;
  NxtSta.FwdSrc := Other;
--
  Sta := NxtSta;
endrule;
endruleset;

ruleset src : NODE do
rule "ABS_NI_Remote_GetX_Nak_dst"
Sta.Env_o & Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Other &
  Sta.Dir.Pending & !Sta.Dir.Local &
  Sta.PendReqSrc = src & Sta.FwdCmd = UNI_GetX  -- by Lemma_3
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.UniMsg[src].Cmd := UNI_Nak;
  NxtSta.UniMsg[src].Proc := Other;
  undefine NxtSta.UniMsg[src].Data;
  NxtSta.NakcMsg.Cmd := NAKC_Nakc;
  NxtSta.FwdCmd := UNI_None;
  NxtSta.FwdSrc := src;
--
  Sta := NxtSta;
endrule;
endruleset;

rule "ABS_NI_Remote_GetX_Nak_src_dst"
Sta.Env_o & Sta.Dir.Pending & !Sta.Dir.Local &
  Sta.PendReqSrc = Other & Sta.FwdCmd = UNI_GetX  -- by Lemma_3
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.NakcMsg.Cmd := NAKC_Nakc;
  NxtSta.FwdCmd := UNI_None;
  NxtSta.FwdSrc := Other;
--
  Sta := NxtSta;
endrule;

ruleset dst : NODE do
rule "ABS_NI_Remote_GetX_PutX_src"
Sta.Env_o & dst != Home &
  Sta.Proc[dst].CacheState = CACHE_E &
  Sta.Dir.Pending & !Sta.Dir.Local &
  Sta.PendReqSrc = Other & Sta.FwdCmd = UNI_GetX  -- by Lemma_3
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.Proc[dst].CacheState := CACHE_I;
  undefine NxtSta.Proc[dst].CacheData;
  NxtSta.ShWbMsg.Cmd := SHWB_FAck;
  NxtSta.ShWbMsg.Proc := Other;
  undefine NxtSta.ShWbMsg.Data;
  NxtSta.FwdCmd := UNI_None;
  NxtSta.FwdSrc := Other;
--
  Sta := NxtSta;
endrule;
endruleset;

ruleset src : NODE do
rule "ABS_NI_Remote_GetX_PutX_dst"
Sta.Env_o & Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Other &
  Sta.Dir.Dirty & Sta.WbMsg.Cmd != WB_Wb & Sta.ShWbMsg.Cmd != SHWB_ShWb &
  forall p : NODE do Sta.Proc[p].CacheState != CACHE_E end &
  Sta.UniMsg[Home].Cmd != UNI_Put &
  forall q : NODE do Sta.UniMsg[q].Cmd != UNI_PutX end &  -- by Lemma_1
  Sta.Dir.Pending & !Sta.Dir.Local &
  Sta.PendReqSrc = src & Sta.FwdCmd = UNI_GetX  -- by Lemma_3
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.UniMsg[src].Cmd := UNI_PutX;
  NxtSta.UniMsg[src].Proc := Other;
  NxtSta.UniMsg[src].Data := Sta.CurrData;  -- by Lemma_5
  if (src != Home) then
    NxtSta.ShWbMsg.Cmd := SHWB_FAck;
    NxtSta.ShWbMsg.Proc := src;
    undefine NxtSta.ShWbMsg.Data;
  end;
  NxtSta.FwdCmd := UNI_None;
  NxtSta.FwdSrc := src;
--
  Sta := NxtSta;
endrule;
endruleset;

rule "ABS_NI_Remote_GetX_PutX_src_dst"
Sta.Env_o & Sta.Dir.Dirty & Sta.WbMsg.Cmd != WB_Wb & Sta.ShWbMsg.Cmd != SHWB_ShWb &
  forall p : NODE do Sta.Proc[p].CacheState != CACHE_E end &
  Sta.UniMsg[Home].Cmd != UNI_Put &
  forall q : NODE do Sta.UniMsg[q].Cmd != UNI_PutX end &  -- by Lemma_1
  Sta.Dir.Pending & !Sta.Dir.Local &
  Sta.PendReqSrc = Other & Sta.FwdCmd = UNI_GetX  -- by Lemma_3
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.ShWbMsg.Cmd := SHWB_FAck;
  NxtSta.ShWbMsg.Proc := Other;
  undefine NxtSta.ShWbMsg.Data;
  NxtSta.FwdCmd := UNI_None;
  NxtSta.FwdSrc := Other;
--
  Sta := NxtSta;
endrule;

rule "ABS_NI_InvAck"
Sta.Env_o & Sta.Dir.Pending & Sta.Collecting &
  Sta.NakcMsg.Cmd = NAKC_None & Sta.ShWbMsg.Cmd = SHWB_None &
  forall q : NODE do
    ( Sta.UniMsg[q].Cmd = UNI_Get | Sta.UniMsg[q].Cmd = UNI_GetX ->
      Sta.UniMsg[q].Proc = Home ) &
    ( Sta.UniMsg[q].Cmd = UNI_PutX ->
      Sta.UniMsg[q].Proc = Home & Sta.PendReqSrc = q )
  end  -- Lemma_4
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  if (exists p : NODE do Sta.Dir.InvSet[p] end) then
    NxtSta.LastInvAck := Other;
    for p : NODE do
      if (Sta.Dir.InvSet[p]) then
        NxtSta.LastOtherInvAck := p;
      end;
    end;
  else
    NxtSta.Dir.Pending := false;
    if (Sta.Dir.Local & !Sta.Dir.Dirty) then
      NxtSta.Dir.Local := false;
    end;
    NxtSta.Collecting := false;
    NxtSta.LastInvAck := Other;
  end;
--
  Sta := NxtSta;
endrule;

rule "ABS_NI_ShWb"
Sta.Env_o & Sta.ShWbMsg.Cmd = SHWB_ShWb &
  Sta.ShWbMsg.Proc = Other
==>
var NxtSta : STATE;
begin
  NxtSta := Sta;
--
  NxtSta.ShWbMsg.Cmd := SHWB_None;
  undefine NxtSta.ShWbMsg.Proc;
  undefine NxtSta.ShWbMsg.Data;
  NxtSta.Dir.Pending := false;
  NxtSta.Dir.Dirty := false;
  NxtSta.Dir.ShrVld := true;
  for p : NODE do
    NxtSta.Dir.ShrSet[p] := Sta.Dir.ShrSet[p];
    NxtSta.Dir.InvSet[p] := Sta.Dir.ShrSet[p];
  end;
  NxtSta.MemData := Sta.ShWbMsg.Data;
--
  Sta := NxtSta;
endrule;

-------------------------------------------------------------------------------


invariant "Lemma_1"
  forall h : NODE do forall dst : NODE do
    h = Home & Sta.Proc[dst].CacheState = CACHE_E ->
    Sta.Dir.Dirty & Sta.WbMsg.Cmd != WB_Wb & Sta.ShWbMsg.Cmd != SHWB_ShWb &
    forall p : NODE do p != dst -> Sta.Proc[p].CacheState != CACHE_E end &
    Sta.UniMsg[h].Cmd != UNI_Put &
    forall q : NODE do Sta.UniMsg[q].Cmd != UNI_PutX end
  end end;


invariant "Lemma_2"
  forall h : NODE do forall src : NODE do forall dst : NODE do
    h = Home & src != dst & dst != h &
    Sta.UniMsg[src].Cmd = UNI_Get & Sta.UniMsg[src].Proc = dst ->
    Sta.Dir.Pending & !Sta.Dir.Local &
    Sta.PendReqSrc = src & Sta.FwdCmd = UNI_Get
  end end end;

invariant "Lemma_3"
  forall h : NODE do forall src : NODE do forall dst : NODE do
    h = Home & src != dst & dst != h &
    Sta.UniMsg[src].Cmd = UNI_GetX & Sta.UniMsg[src].Proc = dst ->
    Sta.Dir.Pending & !Sta.Dir.Local &
    Sta.PendReqSrc = src & Sta.FwdCmd = UNI_GetX
  end end end;

invariant "Lemma_4"
  forall h : NODE do forall p : NODE do
    h = Home & p != h & Sta.InvMsg[p].Cmd = INV_InvAck ->
    Sta.Dir.Pending & Sta.Collecting &
    Sta.NakcMsg.Cmd = NAKC_None & Sta.ShWbMsg.Cmd = SHWB_None &
    forall q : NODE do
      ( Sta.UniMsg[q].Cmd = UNI_Get | Sta.UniMsg[q].Cmd = UNI_GetX ->
        Sta.UniMsg[q].Proc = h ) &
      ( Sta.UniMsg[q].Cmd = UNI_PutX ->
        Sta.UniMsg[q].Proc = h & Sta.PendReqSrc = q )
    end
  end end;

invariant "Lemma_5"
  forall p : NODE do
    Sta.Proc[p].CacheState = CACHE_E -> Sta.Proc[p].CacheData = Sta.CurrData
  end;

/* Correct Set of Invariants Commented on Sep 11, 2013 -- proof holds for these only
invariant "Progress_no_forwarding"
forall src: NODE do
  forall dst: NODE do
   ((isundefined(Sta.PendReqSrc))&(isundefined(Sta.UniMsg[src].Proc)))->progress(src,dst)
  end
end;

invariant "Progress_Interactions_Forwarding"
forall src: NODE do
  forall dst: NODE do
    (!isundefined(Sta.UniMsg[src].Proc) & (dst=Sta.UniMsg[src].Proc))->(progress(src,dst))
  end
end;

invariant "Progress_Interactions_Pending"
forall src: NODE do
  forall dst: NODE do
    ((!isundefined(Sta.PendReqSrc)) & (src=Sta.PendReqSrc) & (isundefined(Sta.UniMsg[Sta.PendReqSrc].Proc)) & (!Sta.Collecting) )->(progress(src, dst))
  end
end;

invariant "Progress_Interactions_Pending"
forall src: NODE do
  forall dst: NODE do
    ((!isundefined(Sta.PendReqSrc))  & (src=Sta.PendReqSrc) & (!isundefined(Sta.UniMsg[Sta.PendReqSrc].Proc)) & (dst=Sta.UniMsg[Sta.PendReqSrc].Proc) & (!Sta.Collecting) )->(progress(src, dst))
  end
end;

invariant "sanity"
((!isundefined(Sta.PendReqSrc))&(Sta.Collecting)&(isundefined(Sta.LastOtherInvAck))) -> false;

invariant "Progress_Invalidate"
forall src: NODE do
  ((!isundefined(Sta.PendReqSrc))&(Sta.Collecting)& (!isundefined(Sta.LastOtherInvAck)) & (src=Sta.LastOtherInvAck)) -> progress_invalidate(src)
end;
*/

/* COmmented at 218 am.
invariant "Progress_initial"
forall src: NODE do
  forall dst: NODE do
    (isundefined(Sta.PendReqSrc))->progress(src,dst)
  end
end;

invariant "Progress_Interactions_Pending_No_Forwarding"
forall src: NODE do
  forall dst: NODE do
  ((!isundefined(Sta.PendReqSrc)) & (Sta.PendReqSrc = src) & (isundefined(Sta.UniMsg[Sta.PendReqSrc].Proc)) & (!Sta.Collecting))->(progress(Sta.PendReqSrc, dst))
   end
end;

invariant "Progress_Interactions_Pending_Forwarding"
forall src: NODE do
  forall dst: NODE do
    ((!isundefined(Sta.PendReqSrc)) & (Sta.PendReqSrc = src) & (!isundefined(Sta.UniMsg[Sta.PendReqSrc].Proc)) & (!Sta.Collecting) & (Sta.UniMsg[Sta.PendReqSrc].Proc = dst))->(progress(src, dst))
   end
end;

invariant "Progress_Invalidate"
forall src:NODE do
 ((!isundefined(Sta.PendReqSrc))&(Sta.Collecting)& (!isundefined(Sta.LastOtherInvAck)) & (Sta.LastOtherInvAck = src)) -> progress_invalidate(src)
end;

invariant "sanity"
((!isundefined(Sta.PendReqSrc))&(Sta.Collecting)&(isundefined(Sta.LastOtherInvAck))) -> false;
*/


/*
--Step 1:

invariant "Progress_initial" Failed since cant happen for all src when pendreqsrc valid.
forall src: NODE do
  forall dst: NODE do
    true->progress(src,dst)
  end
end;
*/

/*
--Step 2

invariant "Progress_noPending"
forall src: NODE do
  forall dst: NODE do
    (isundefined(Sta.PendReqSrc))->progress(src,dst)
  end
end;


failed since does not work if proccmd valid

invariant "Progress_Pending"
forall src: NODE do
  forall dst: NODE do
    (!isundefined(Sta.PendReqSrc)) & (src = Sta.PendReqSrc)->progress(src,dst)
  end
end;
*/

/* Step 3
invariant "Progress_noPending"
forall src: NODE do
  forall dst: NODE do
    (isundefined(Sta.PendReqSrc))->progress(src,dst)
  end
end;

-- Failed since collecting true (invalidate)
invariant "Progress_Pending_unknownForwardingDst"
forall src: NODE do
  forall dst: NODE do
    (!isundefined(Sta.PendReqSrc)) & (src = Sta.PendReqSrc)  & (isundefined(Sta.UniMsg[Sta.PendReqSrc].Proc)) -> progress(src,dst)
  end
end;


invariant "Progress_Pending_knownForwardingDst"
forall src: NODE do
  forall dst: NODE do
    (!isundefined(Sta.PendReqSrc)) & (src = Sta.PendReqSrc)  & (!isundefined(Sta.UniMsg[Sta.PendReqSrc].Proc) & (dst = Sta.UniMsg[Sta.PendReqSrc].Proc)) ->progress(src,dst)
  end
end;
*/

invariant "Progress_noPending"
forall src: NODE do
  forall dst: NODE do
    (isundefined(Sta.PendReqSrc))->progress(src,dst)
  end
end;

invariant "Progress_Pending_unknownForwardingDstNoInv"
forall src: NODE do
  forall dst: NODE do
    (!isundefined(Sta.PendReqSrc)) & (src = Sta.PendReqSrc)  & (isundefined(Sta.UniMsg[Sta.PendReqSrc].Proc)) & isundefined(Sta.LastOtherInvAck)
-> progress(src,dst)
  end
end;


invariant "Progress_Pending_unknownForwardingDstInv"
forall src: NODE do
  forall dst: NODE do
    (!isundefined(Sta.PendReqSrc)) & !isundefined(Sta.LastOtherInvAck) & (src = Sta.LastOtherInvAck)  & (isundefined(Sta.UniMsg[Sta.PendReqSrc].Proc)) 
-> progress(src,dst)
  end
end;


invariant "Progress_Pending_knownForwardingDst"
forall src: NODE do
  forall dst: NODE do
    (!isundefined(Sta.PendReqSrc)) & (src = Sta.PendReqSrc)  & (!isundefined(Sta.UniMsg[Sta.PendReqSrc].Proc) & (dst = Sta.UniMsg[Sta.PendReqSrc].Proc)) ->progress(src,dst)
  end
end;
