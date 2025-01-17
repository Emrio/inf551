all:
	dune exec ./prover.exe --no-print-directory

# You can add more tests here
test:
	for f in proofs/*.proof; do \
		if (cat $$f | dune exec ./prover.exe --no-print-directory 2> /dev/null | grep -q 'Typechecking... ok.') then \
			echo "$$f OK"; \
		else \
			echo ""; cat $$f | dune exec ./prover.exe --no-print-directory; echo "^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n$$f NOT OK\n"; \
		fi; \
	done
