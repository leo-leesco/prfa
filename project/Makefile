all: Makefile.rocq
	$(MAKE) -f Makefile.rocq

clean: Makefile.rocq
	$(MAKE) -f Makefile.rocq clean
	rm -f Makefile.*
	rm -f .*.aux

Makefile.rocq:
	rocq makefile -f _RocqProject -o Makefile.rocq

.PHONY: all clean
