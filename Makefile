COQC := coqc
sources = expr expr_db_nat bisim db cem cbn

all: ${sources}

%: %.v
	${COQC} $<

clean:
	rm -f *.glob *.vo
