NAME     = fiat-shamir-zkp

OCAMLC   = ocamlfind ocamlc -g
OCAMLL   = $(OCAMLC) -package "$(REQUIRES)" -linkpkg nums.cma cryptokit.cma
OCAMLOPT = ocamlfind ocamlopt -package "$(REQUIRES)" -linkpkg \
nums.cmxa cryptokit.cmxa
OCAMLDEP = ocamldep

EXECS = zkp-prove zkp-check

OBJECTS = 
XOBJECTS = 
ARCHIVE  = $(NAME).cma
XARCHIVE = $(NAME).cmxa

REQUIRES = unix
PREDICATES =

.PHONY: all pkg optpkg

all: $(EXECS)

#zkp-prove: bn.cmo lowlife.cmo config.cmo zkp-prove.cmo
#	$(OCAMLL) $^ -o $@

zkp-prove: bn.cmx lowlife.cmx config.cmx zkp-prove.cmx
	$(OCAMLOPT) $^ -o $@

#zkp-check: bn.cmo lowlife.cmo config.cmo zkp-check.cmo
#	$(OCAMLL) $^ -o $@

zkp-check: bn.cmx lowlife.cmx config.cmx zkp-check.cmx
	$(OCAMLOPT) $^ -o $@

pkg: $(ARCHIVE)
optpkg: $(XARCHIVE)

$(ARCHIVE): $(OBJECTS)
	$(OCAMLC) -a -o $(ARCHIVE) -package "$(REQUIRES)" -linkpkg \
	-predicates "$(PREDICATES)" $(OBJECTS)
$(XARCHIVE): $(XOBJECTS)
	$(OCAMLOPT) -a -o $(XARCHIVE) -package "$(REQUIRES)"  $(XOBJECTS)
# -linkpkg \
#	-predicates "$(PREDICATES)" $(XOBJECTS)

.SUFFIXES: .cmo .cmi .cmx .ml .mli

.ml.cmo:
	$(OCAMLC) -package "$(REQUIRES)" -predicates "$(PREDICATES)" \
	-c $<
.mli.cmi:
	$(OCAMLC) -package "$(REQUIRES)" -predicates "$(PREDICATES)" \
	-c $<
.ml.cmx:
	$(OCAMLOPT) -package "$(REQUIRES)" -predicates "$(PREDICATES)" \
	-c $<

include depend

depend: $(wildcard *.ml*)
	if ! ($(OCAMLDEP) *.mli *.ml >depend); then rm depend; fi

.PHONY: install uninstall clean

install: all
	{ test ! -f $(XARCHIVE) || extra="$(XARCHIVE) "`basename $(XARCHIVE) .cmxa`.a }; \
	ocamlfind install $(NAME) *.mli *.cmi $(ARCHIVE) META $$extra

uninstall:
	ocamlfind remove $(NAME)

clean:
	rm -f depend *.cmi *.cmo *.cmx *.cma *.cmxa *.a *.o $(EXECS)
	rm -f depend *.dvi *.log *.aux *.ps
