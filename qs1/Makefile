.PHONY: all test clean results bools

all: test

test: results
	diff -u specimen-results results

specimen-results: results
	cp $< $@

results: Examples
	rm -f $@
	@($(foreach test, hamt,\
		echo $(test): &&\
		(time -f "real %es / user %Us / sys %Ss" ./Examples $(test) ) && echo && ) true) | tee $@

bools nats lists heaps arrays comp queues pretty regex queuesM arraysM tinywm: Examples
	zsh -i -c "bench ./Examples $@"

Examples: *.hs
	ghc --make -Odph -O2 Examples.hs \
		-fllvm -optlo-O3 -optlc-O3 \
		-funbox-strict-fields \
		-ignore-package monads-fd \
		-ignore-package monads-tf \
		-package mtl-1.1.1.1 \
		-package parallel

clean:
	rm -f Examples *.hi *.o
