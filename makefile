MD2HTML ?= md2html
PORT ?= 8001
HOST ?= 127.0.0.1

.PHONY: all build html markdown rebuild serve watch clean

all: build markdown

build html:
	$(MD2HTML)

markdown:
	$(MD2HTML) --jekyll-markdown -o markdown-output

rebuild:
	$(MD2HTML) --clean --force

serve:
	$(MD2HTML) -es --host $(HOST) --port $(PORT)

watch:
	$(MD2HTML) --watch

clean:
	rm -rf html markdown-output
