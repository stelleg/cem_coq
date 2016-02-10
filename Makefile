COQC := coqc
sources = CpdtTactics util expr expr_db_nat bisim db cem cbn assembly compiler

all: ${sources}

%: %.v
	${COQC} $<

clean:
	rm -f *.glob *.vo
