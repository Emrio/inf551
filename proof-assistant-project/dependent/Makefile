all:
	dune exec ./prover.exe --no-print-directory

test:
	for f in proofs/*.proof; do \
		if (cat $$f | dune exec ./prover.exe --no-print-directory 2> /dev/null | grep -q 'Typing error') then \
			echo ""; cat $$f | dune exec ./prover.exe --no-print-directory; echo "^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n$$f NOT OK\n"; \
		else \
			echo "$$f OK"; \
		fi; \
	done
