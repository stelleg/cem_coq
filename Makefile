COQC := coqc
%: %.v
	${COQC} $<