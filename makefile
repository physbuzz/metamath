MD2HTML ?= md2html
PORT ?= 8001
HOST ?= 127.0.0.1

.PHONY: all build html rebuild serve watch clean

all: build

build html:
	$(MD2HTML)

rebuild:
	$(MD2HTML) --clean --force

serve:
	$(MD2HTML) -es --host $(HOST) --port $(PORT)

watch:
	$(MD2HTML) --watch

clean:
	rm -rf html
