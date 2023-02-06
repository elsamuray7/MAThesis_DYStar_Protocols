include ../../Makefile

APP_BASE_FST_FILES=YLM.Messages.fst YLM.Sessions.fst
APP_BASE_CMX_FILES=ocaml-symbolic/YLM_Messages.cmx ocaml-symbolic/YLM_Sessions.cmx

APP_FST_FILES=YLM.Protocol.fst YLM.Debug.fst
APP_CMX_FILES=ocaml-symbolic/YLM_Protocol.cmx ocaml-symbolic/YLM_Debug.cmx

ALL_FST_FILES=$(LIB_BASE_FST_FILES) $(APP_BASE_FST_FILES) $(LIB_FST_FILES) $(APP_FST_FILES)
ALL_CMX_FILES=$(LIB_BASE_CMX_FILES) $(APP_BASE_CMX_FILES) $(LIB_CMX_FILES) $(APP_CMX_FILES)

extract: $(ALL_FST_FILES) $(ALL_CMX_FILES)
test: $(ALL_FST_FILES) $(ALL_CMX_FILES) ocaml-symbolic/test.exe

ocaml-symbolic/test.exe: $(ALL_CMX_FILES)
	$(OCAMLOPT) $^ -o $@
