all: result/bin/bytestring-fiat

result/bin/bytestring-fiat: HeapFMapExt.hs	\
	HString.hs				\
	Main.hs					\
	Setup.hs				\
	default.nix				\
	bytestring-fiat.cabal
	nix-build -E 'let pkgs = import <nixpkgs> {}; in pkgs.stdenv.lib.callPackageWith (pkgs // pkgs.haskell.packages.ghc7103) ./default.nix {}'

HeapFMapExt.hs: Makefile.coq			\
	ADTInduction.v				\
	BindDep.v				\
	ByteString.v				\
	ByteStringLib.v				\
	Comp.v					\
	Composition.v				\
	Decidable.v				\
	DefineAbsR.v				\
	FMapExt.v				\
	FromADT.v				\
	FunMaps.v				\
	Heap.v					\
	HeapADT.v				\
	HeapFMap.v				\
	HeapFMapExt.v				\
	LibExt.v				\
	MemoryBlockC.v				\
	Nomega.v				\
	Pending.v				\
	Pipes.v					\
	Refined.v				\
	RefinedLib.v				\
	Relations.v				\
	Same_set.v				\
	Tactics.v				\
	TupleEnsembles.v			\
	TupleEnsemblesDep.v			\
	TupleEnsemblesFinite.v			\
	Within.v				\
	fixcode.pl
	make -f Makefile.coq && perl -i fixcode.pl $@

Makefile.coq: ../_CoqProject
	coq_makefile -f $< -o $@

clean: Makefile.coq
	make -f Makefile.coq clean
	rm -f *.glob *.v.d *.vo *.hi *.o Main result *.hp .*.aux
	rm -f bytestring-fiat HeapFMapExt.hs
