# Makefile in small2

hola: hola.c
	gcc -g -Wall -o hola hola.c
	./hola

holabox: holabox.c
	gcc -g -Wall -o holabox -D_GNUCC -Dx86_LINUX -DBEFOREBOX \
		-I /home/scott/wrk/safec/cil/lib \
		./holabox.c \
		/home/scott/wrk/safec/cil/lib/../obj/safecdebuglib.a

# sm: clean-cvsignore is a script of mine, I make it ok to fail below
clean:
	rm -f *.o *_all.c *cil.c *box.c *_ppp.c *.i *.origi *infer.c *cabs.c
	rm -f comb enuminit multiplestatics staticafternostorage
	rm -f hola partialbracket ptrtolocal rmunused recursetype
	rm -f regbeforeassign simplewild tprintf voidfree
	rm -f *.exe *.obj *.pdb *.ilk
	rm -f __scalar2pointer.txt ocamlprof.dump "#"*
	rm -f *cured.c *.optim.c *_comb.c
	rm -rf *.browser
	clean-cvsignore || true

