all: ByteString

ByteString: Makefile.coq			\
	ADTInduction.v				\
	ByteString.v				\
	ByteStringLib.v				\
	Canonical.v				\
	FixedPoint.v				\
	Heap.v					\
	IEnsemble.v				\
	LibExt.v				\
	Properties.v				\
	Refined.v				\
	RefinedLib.v
	make -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@

clean: _CoqProject Makefile.coq
	make -f Makefile.coq clean
	rm -f *.glob *.v.d *.vo *.hi *.o Main result *.hp .*.aux
	rm -f ByteString ByteString.hs

fullclean: clean
	rm -f Makefile
