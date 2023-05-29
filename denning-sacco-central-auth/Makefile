include ../../Makefile

APP_BASE_FST_FILES=DS.Helper.fst DS.Messages.fst DS.Sessions.fst DS.Clock.fst DS.SendRecv.fst
APP_BASE_CMX_FILES=ocaml-symbolic/DS_Helper.cmx ocaml-symbolic/DS_Messages.cmx ocaml-symbolic/DS_Sessions.cmx ocaml-symbolic/DS_Clock.cmx ocaml-symbolic/DS_SendRecv.cmx

APP_FST_FILES=DS.Protocol.fst DS.Attacker.fst DS.Debug.fst
APP_CMX_FILES=ocaml-symbolic/DS_Protocol.cmx ocaml-symbolic/DS_Attacker.cmx ocaml-symbolic/DS_Debug.cmx

ALL_FST_FILES=$(LIB_BASE_FST_FILES) $(APP_BASE_FST_FILES) $(LIB_FST_FILES) $(APP_FST_FILES)
ALL_CMX_FILES=$(LIB_BASE_CMX_FILES) $(APP_BASE_CMX_FILES) $(LIB_CMX_FILES) $(APP_CMX_FILES)

extract: $(ALL_FST_FILES) $(ALL_CMX_FILES)
test: $(ALL_FST_FILES) $(ALL_CMX_FILES) ocaml-symbolic/test.exe

ocaml-symbolic/test.exe: $(ALL_CMX_FILES)
	$(OCAMLOPT) $^ -o $@
