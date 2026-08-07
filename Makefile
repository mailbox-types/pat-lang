all:
	@if dune build; then\
		ln -sf _build/default/bin/main.exe pat;\
	fi

.PHONY: test
test:
	cd test && python3 run-tests.py

.PHONY: pin
pin:
	opam pin add . --kind=path -y

.PHONY: install
install:
	opam reinstall pat

.PHONY: uninstall
uninstall:
	opam remove pat

.PHONY: clean
clean:
	dune clean
	rm -f pat
