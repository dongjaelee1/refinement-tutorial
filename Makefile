COQMODULE    := Tutorial
COQTHEORIES  := \
	src/lib/*.v \
	src/tutorial/*.v \
	src/tutorial/examples/*.v \
	src/tutorial/advanced_examples/*.v \

.PHONY: all theories clean

all: build

build: Makefile.coq
	$(MAKE) -f Makefile.coq all

quick: Makefile.coq
	$(MAKE) -f Makefile.coq vio

Makefile.coq: Makefile $(COQTHEORIES)
	(echo "-Q src/lib $(COQMODULE)"; \
	 echo "-Q src/tutorial $(COQMODULE)"; \
	 echo "-Q src/tutorial/examples $(COQMODULE)"; \
	 echo "-Q src/tutorial/advanced_examples $(COQMODULE)"; \
   \
   echo $(COQTHEORIES)) > _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

%.vo: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

%.vio: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

clean:
	$(MAKE) -f Makefile.coq clean
	rm -f _CoqProject Makefile.coq Makefile.coq.conf
