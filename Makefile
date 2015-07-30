COQC := coqc
%: %.v
	${COQC} $<

clean:
	rm -f *.glob *.vo
