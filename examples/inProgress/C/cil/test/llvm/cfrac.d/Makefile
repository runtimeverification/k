#
# An implementation of the Continued Fraction Algorithm CFRAC
#
# Dave Barrett
#

PDIR 	= .
# removed because I don't want to recompile every time I change header file
#INCF 	= pfactor.h

ifndef ARCHOS
   $(error "You must define the ARCHOS variable")
endif

LLCIL   = ../../../obj/$(ARCHOS)/cilly.byte.exe --dollvm --envmachine
LLCC    = llvm-as
CC 	= gcc -m32
CFLAGS  = -g -DNOMEMOPT $(EXTRACFLAGS)

BINSRC  = cfrac.c
HDR	= primes.h seive.h pfactor.h

PSRC	= pops.c pconst.c pio.c \
	  pabs.c pneg.c pcmp.c podd.c phalf.c \
	  padd.c psub.c pmul.c pdivmod.c psqrt.c ppowmod.c \
	  atop.c ptoa.c itop.c utop.c ptou.c errorp.c \
	  pfloat.c pidiv.c pimod.c picmp.c

FSRC	= primes.c pcfrac.c pgcd.c

FOBJS	= $(PSRC:.c=.bc)
POBJS	= $(FSRC:.c=.bc)
OBJS	= $(BINSRC:.c=.bc) $(PSRC:.c=.bc) $(FSRC:.c=.bc)

%.bc: %.c
	@mkdir -p temp
	$(CC) -E $(CFLAGS) $< >temp/$*.i
	CIL_MACHINE=`../../../obj/$(ARCHOS)/machdep-ml32.exe --env 2>/dev/null` \
	  $(LLCIL) temp/$*.i >temp/$*.ll
	$(LLCC) -o $@ temp/$*.ll

all: cfrac
	./cfrac 23551

cfrac:	$(OBJS)
	llvm-link -f -o cfrac-all.bc $(OBJS)
	#opt -f -std-compile-opts -o cfrac-opt.bc cfrac-all.bc
	llc -march=x86 -f cfrac-all.bc
	$(CC) -o cfrac cfrac-all.s -lm

malloc:

bwgc:

SRC	= Makefile $(HDR) $(BINSRC)

pgcd.o:		$(INC)
pcfrac.o:	$(INCF) $(INC) primes.h
primes.o:	primes.h

clean:
		rm -rf core temp
		rm -f $(OBJS) cfrac

cleantarget:
	rm cfrac

# 
# producer only clean
#
pclean:	
		rm -f $(OBJS)
