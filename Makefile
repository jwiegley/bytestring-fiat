all: bstring

bstring: Makefile.coq				\
	ADTInduction.v				\
	BindDep.v				\
	ByteString.v				\
	ByteStringLib.v				\
	Decidable.v				\
	FixedPoint.v				\
	FromADT.v				\
	Heap.v					\
	HeapADT.v				\
	IEnsemble.v				\
	LibExt.v				\
	Nomega.v				\
	RefinedHeap.v				\
	Same_set.v
	make -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@

clean: _CoqProject Makefile.coq
	make -f Makefile.coq clean
	rm -f *.glob *.v.d *.vo *.hi *.o Main result *.hp .*.aux
	rm -f bstring bstring.hs

fullclean: clean
	rm -f Makefile
