files = CpdtTactics \
				util \
				expr \
				expr_db_nat \
				bisim \
				db \
				cem \
				cbn \
				assembly \
				cesm \
				compiler 

sources = ${files:=.v}
objects = ${files:=.vo}
deps = ${files:=.d}

all: ${sources}
	$(MAKE) ${deps}
	$(MAKE) ${objects}

%.vo: %.v
	coqc $<

%.d: %.v
	coqdep -I . $< > $@

-include ${deps}

clean:
	rm -f *.glob *.vo *.d

