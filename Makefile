LAKEBIN=lake

PROJECT=PrimeNumberTheoremAnd

FILES=$(basename $(notdir $(wildcard $(PROJECT)/*.lean)))
BLUEPRINTS=$(addsuffix .tex, $(addprefix blueprint/, $(FILES)))
BLUEPRINT_FILE=blueprint/blueprint.tex

build:
	$(LAKEBIN) exe cache get
	$(LAKEBIN) build

doc:
	$(LAKEBIN) -R -Kenv=dev build $(PROJECT):docs
clean-doc:
	rm -rf .lake/build/doc/*

blueprint: clean-blueprint
	python3 leanblueprint-extract/extract_blueprint -O blueprint $(PROJECT)/*.lean
	make -C blueprint
	make -C blueprint clean-aux
clean-blueprint:
	mkdir -p blueprint
	rm -f $(BLUEPRINTS)
	make -C blueprint clean

clean: clean-doc clean-blueprint
