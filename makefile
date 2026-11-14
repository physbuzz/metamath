MD2HTML ?= md2html
PAGEQUIZ ?= pagequiz
MARKDOWN_OUTPUT ?= markdown-output
PORT ?= 8002
HOST ?= 127.0.0.1

.PHONY: all build html markdown quiz rebuild serve watch clean

all: build markdown

build html:
	$(MD2HTML)

markdown:
	$(MD2HTML) --jekyll-markdown -o $(MARKDOWN_OUTPUT)

quiz:
	$(PAGEQUIZ) questions -o html/quiz --template questions/template.html --fonts-output html/assets/mathjax/woff2

rebuild:
	$(MD2HTML) --clean --force

serve:
	$(MD2HTML) -es --host $(HOST) --port $(PORT)


watch:
	$(MD2HTML) --watch

clean:
	rm -rf html markdown-output
