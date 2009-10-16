.PHONY: all test clean results bools

all: test

test: results
	diff -u specimen-results results

specimen-results: results
	cp $< $@

results: Examples
	rm -f $@
	@($(foreach test, nats bools lists heaps,\
		echo $(test): &&\
		(./Examples $(test) | grep "== equations ==" -B 0 -A 9999 | sed 's/^/  /') && echo && ) true) | tee $@

bools nats lists heaps arrays comp queues: Examples
	zsh -i -c "bench ./Examples $@"

Examples: *.hs
	ghc --make -O2 Examples.hs -threaded
