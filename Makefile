##############################################################################
##                 The Calculus of Inductive Constructions                  ##
##                                                                          ##
##                                Projet Coq                                ##
##                                                                          ##
##                     INRIA                        ENS-CNRS                ##
##              Rocquencourt                        Lyon                    ##
##                                                                          ##
##                                  Coq V7                                  ##
##                                                                          ##
##                                                                          ##
##############################################################################

# WARNING
#
# This Makefile has been automagically generated by coq_makefile
# Edit at your own risks !
#
# END OF WARNING

#
# This Makefile was generated by the command line :
# coq_makefile -f Make -o Makefile 
#

##########################
#                        #
# Variables definitions. #
#                        #
##########################

CAMLP4LIB=`camlp4 -where`
COQSRC=-I $(COQTOP)/kernel -I $(COQTOP)/lib \
  -I $(COQTOP)/library -I $(COQTOP)/parsing \
  -I $(COQTOP)/pretyping -I $(COQTOP)/interp \
  -I $(COQTOP)/proofs -I $(COQTOP)/syntax -I $(COQTOP)/tactics \
  -I $(COQTOP)/toplevel -I $(COQTOP)/contrib/correctness \
  -I $(COQTOP)/contrib/extraction -I $(COQTOP)/contrib/field \
  -I $(COQTOP)/contrib/fourier -I $(COQTOP)/contrib/graphs \
  -I $(COQTOP)/contrib/interface -I $(COQTOP)/contrib/jprover \
  -I $(COQTOP)/contrib/omega -I $(COQTOP)/contrib/romega \
  -I $(COQTOP)/contrib/ring -I $(COQTOP)/contrib/xml \
  -I $(CAMLP4LIB)
ZFLAGS=$(OCAMLLIBS) $(COQSRC)
OPT=
COQFLAGS=-q $(OPT) $(COQLIBS) $(COQ_XML)
COQC=$(COQBIN)coqc
GALLINA=gallina
COQDOC=coqdoc
CAMLC=ocamlc -c
CAMLOPTC=ocamlopt -c
CAMLLINK=ocamlc
CAMLOPTLINK=ocamlopt
COQDEP=$(COQBIN)coqdep -c
COQVO2XML=coq_vo2xml
GRAMMARS=grammar.cma
CAMLP4EXTEND=pa_extend.cmo pa_ifdef.cmo q_MLast.cmo
PP=-pp "camlp4o -I . -I $(COQTOP)/parsing $(CAMLP4EXTEND) $(GRAMMARS) -impl"

#########################
#                       #
# Libraries definition. #
#                       #
#########################

OCAMLLIBS=-I .
COQLIBS=-I .

###################################
#                                 #
# Definition of the "all" target. #
#                                 #
###################################

VFILES=
VOFILES=$(VFILES:.v=.vo)
VIFILES=$(VFILES:.v=.vi)
GFILES=$(VFILES:.v=.g)
HTMLFILES=$(VFILES:.v=.html)
GHTMLFILES=$(VFILES:.v=.g.html)

all: lib_arith\
  logique\
  reachable\
  card\
  gc\
  lemma_step\
  safety\
  mesure\
  liveness

###################
#                 #
# Subdirectories. #
#                 #
###################

lib_arith:
	cd lib_arith ; $(MAKE) all

logique:
	cd logique ; $(MAKE) all

reachable:
	cd reachable ; $(MAKE) all

card:
	cd card ; $(MAKE) all

gc:
	cd gc ; $(MAKE) all

lemma_step:
	cd lemma_step ; $(MAKE) all

safety:
	cd safety ; $(MAKE) all

mesure:
	cd mesure ; $(MAKE) all

liveness:
	cd liveness ; $(MAKE) all

####################
#                  #
# Special targets. #
#                  #
####################

.PHONY: all opt byte archclean clean install depend xml lib_arith logique reachable card gc lemma_step safety mesure liveness

byte:
	$(MAKE) all "OPT="

opt:
	$(MAKE) all "OPT=-opt"

.depend depend:
	(cd lib_arith ; $(MAKE) depend)
	(cd logique ; $(MAKE) depend)
	(cd reachable ; $(MAKE) depend)
	(cd card ; $(MAKE) depend)
	(cd gc ; $(MAKE) depend)
	(cd lemma_step ; $(MAKE) depend)
	(cd safety ; $(MAKE) depend)
	(cd mesure ; $(MAKE) depend)
	(cd liveness ; $(MAKE) depend)

xml::
	(cd lib_arith ; $(MAKE) xml)
	(cd logique ; $(MAKE) xml)
	(cd reachable ; $(MAKE) xml)
	(cd card ; $(MAKE) xml)
	(cd gc ; $(MAKE) xml)
	(cd lemma_step ; $(MAKE) xml)
	(cd safety ; $(MAKE) xml)
	(cd mesure ; $(MAKE) xml)
	(cd liveness ; $(MAKE) xml)

install:
	mkdir -p `$(COQC) -where`/user-contrib
	(cd lib_arith ; $(MAKE) install)
	(cd logique ; $(MAKE) install)
	(cd reachable ; $(MAKE) install)
	(cd card ; $(MAKE) install)
	(cd gc ; $(MAKE) install)
	(cd lemma_step ; $(MAKE) install)
	(cd safety ; $(MAKE) install)
	(cd mesure ; $(MAKE) install)
	(cd liveness ; $(MAKE) install)

Makefile: Make
	mv -f Makefile Makefile.bak
	$(COQBIN)coq_makefile -f Make -o Makefile

clean:
	rm -f *.cmo *.cmi *.cmx *.o *.vo *.vi *.g *~
	rm -f all.ps all-gal.ps $(HTMLFILES) $(GHTMLFILES)
	(cd lib_arith ; $(MAKE) clean)
	(cd logique ; $(MAKE) clean)
	(cd reachable ; $(MAKE) clean)
	(cd card ; $(MAKE) clean)
	(cd gc ; $(MAKE) clean)
	(cd lemma_step ; $(MAKE) clean)
	(cd safety ; $(MAKE) clean)
	(cd mesure ; $(MAKE) clean)
	(cd liveness ; $(MAKE) clean)

archclean:
	rm -f *.cmx *.o
	(cd lib_arith ; $(MAKE) archclean)
	(cd logique ; $(MAKE) archclean)
	(cd reachable ; $(MAKE) archclean)
	(cd card ; $(MAKE) archclean)
	(cd gc ; $(MAKE) archclean)
	(cd lemma_step ; $(MAKE) archclean)
	(cd safety ; $(MAKE) archclean)
	(cd mesure ; $(MAKE) archclean)
	(cd liveness ; $(MAKE) archclean)

# WARNING
#
# This Makefile has been automagically generated by coq_makefile
# Edit at your own risks !
#
# END OF WARNING

