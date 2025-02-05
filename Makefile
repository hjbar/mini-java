
all: clean fmt minijava.exe test

test-compile:
	@cd tests && ./test -3 ../minijava.exe

test-typing:
	@cd tests && ./test -2 ../minijava.exe

test:
	@./minijava.exe --debug test/test.java
	@gcc -no-pie -g test/test.s -o test/a.out && ./test/a.out

minijava.exe:
	@dune build src/minijava.exe
	@mv _build/default/src/minijava.exe .

clean:
	@dune clean
	@find . -type f -name "*.exe" -delete
	@find . -type f -name "*.s" -delete
	@find . -type f -name "a.out" -delete

fmt:
	@dune fmt

.PHONY: all fmt clean minijava.exe test test-typing test-compile
