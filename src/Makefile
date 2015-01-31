all:
	ocamlc -c ListMore.ml
	ocamlc -c Fixpoint.ml
	ocamlc -c Fixpoint.cmo Prop.ml
	ocamlc -c Fixpoint.cmo ProcImp.ml
	ocamlc -c PDS.ml
	ocamlc -c ListMore.cmo SCTPLB.ml
	ocamlc -c Fixpoint.cmo Prop.cmo APDS.ml
	ocamlc -c ListMore.cmo Fixpoint.cmo Prop.cmo APDS.cmo AMA.ml
	ocamlc -c ListMore.cmo Fixpoint.cmo Prop.cmo ProcImp.cmo PDS.cmo APDS.cmo AMA.cmo SCTPLB.cmo CFG.ml

	ocaml ModelChecking.ml


clean:
	rm -fR *.cmo
	rm -fR *.cmi
	rm -fR *.cmx
	rm -fR *.o
	rm -fR a.out


test:
	ocamlopt -c ListMore.ml
	ocamlopt -c Fixpoint.ml
	ocamlopt -c Fixpoint.cmx Prop.ml
	ocamlopt -c Fixpoint.cmx ProcImp.ml
	ocamlopt -c PDS.ml
	ocamlopt -c ListMore.cmx SCTPLB.ml
	ocamlopt -c Fixpoint.cmx Prop.cmx APDS.ml
	ocamlopt -c ListMore.cmx Fixpoint.cmx Prop.cmx APDS.cmx AMA.ml
	ocamlopt -c ListMore.cmx Fixpoint.cmx Prop.cmx ProcImp.cmx PDS.cmx APDS.cmx AMA.cmx SCTPLB.cmx CFG.ml
	ocamlopt ListMore.cmx Fixpoint.cmx Prop.cmx ProcImp.cmx PDS.cmx APDS.cmx AMA.cmx SCTPLB.cmx CFG.cmx Test.ml
	./iter.sh 
