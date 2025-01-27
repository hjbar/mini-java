
all: fmt minijava.exe
	@./minijava.exe --debug test.java
	@gcc -no-pie -g test.s && ./a.out

minijava.exe:
	@dune build minijava.exe

clean:
	@dune clean

fmt:
	@dune fmt

.PHONY: all fmt clean minijava.exe
