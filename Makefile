COQC := coqc
%: %.v
	${COQC} $<
