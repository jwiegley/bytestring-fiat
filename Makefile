MISSING	 =									\
	find src \( \( -name coq-haskell -o -name fiat \) -prune \)		\
	    -o \( -name '*.v'							\
		! -name fiat							\
		! -name coq-haskell -print \)				|	\
		xargs egrep -i -Hn '(abort|admit|undefined|jww)'	|	\
		      egrep -v 'Definition undefined'			|	\
		      egrep -v '(old|new|research)/'

all: bstring
	-@$(MISSING) || exit 0

bstring: Makefile.coq $(wildcard *.v)
	rm -f ByteStringExt.hs
	touch extract/ByteStringExt.v
	make -f Makefile.coq -j
	perl -i extract/fixcode.pl ByteStringExt.hs
	mv ByteStringExt.hs extract
	(cd extract; nix-cabal-build)

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@

clean: _CoqProject Makefile.coq
	make -f Makefile.coq clean
	(cd src; rm -f *.glob *.v.d *.vo *.hi *.o Main result *.hp .*.aux)
	rm -f bstring bstring.hs

fullclean: clean
	rm -f Makefile.coq
