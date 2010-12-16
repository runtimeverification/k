# $Id: Makefile,v 1.15 2007-11-14 09:11:59 deraugla Exp $

OCAMLC   = ocamlc
CAMLP5   = "camlp5r pa_macro.cmo"
OCAMLOPT = ocamlopt
OCAMLDEP = ocamldep
LIBDIR = `ocamlc -where`

OBJS=pa_ioXML.cmo ioXML.cmo ioXML.cmi
OBJS_OPT=ioXML.cmx ioXML.o

byte: $(OBJS)
all: byte opt
opt: $(OBJS_OPT)

clean:
	rm -f *.cm[oix] *.o

.depend:
	$(OCAMLDEP) -pp $(CAMLP5) *.ml* > .depend

depend: .depend

install:
	cp -f $(OBJS) ioXML.mli $(LIBDIR)/camlp5
	if test -f ioXML.cmx ; then cp -f $(OBJS_OPT) $(LIBDIR)/camlp5/.; fi

rminstall:
	cd $(LIBDIR)/camlp5; rm $(OBJS) ioXML.mli; rm -f $(OBJS_OPT)

pa_ioXML.cmo: pa_ioXML.ml
	@if test `basename $<` != $<; then echo "Bad directory"; exit 1; fi
	$(OCAMLC) -pp $(CAMLP5) -I `camlp5 -where` -c $<

.SUFFIXES: .mli .ml .cmi .cmo .cmx

.mli.cmi:
	@if test `basename $<` != $<; then echo "Bad directory"; exit 1; fi
	$(OCAMLC) -pp $(CAMLP5) -c $<

.ml.cmo:
	@if test `basename $<` != $<; then echo "Bad directory"; exit 1; fi
	$(OCAMLC) -pp $(CAMLP5) -c $<

.ml.cmx:
	@if test `basename $<` != $<; then echo "Bad directory"; exit 1; fi
	$(OCAMLOPT) -pp $(CAMLP5) -c $<

include .depend
