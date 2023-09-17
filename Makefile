idris2 = idris2

build: TRTC trtc.ipkg FORCE
	$(idris2) --build trtc.ipkg

FORCE:

clean:
	$(idris2) --clean trtc.ipkg
	rm -r .build

typecheck:
	$(idris2) --typecheck trtc.ipkg

repl:
	$(idris2) --repl trtc.ipkg
