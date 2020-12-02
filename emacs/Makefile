GENERATE=generate-edits-mode.rb
PARSERS=../src/lib/HsToCoq/Edits/Parser.y
EDITS=edits.el

all: $(EDITS)

$(EDITS): $(GENERATE) $(PARSERS)
	./$(GENERATE) $(PARSERS) > $(EDITS)

clean:
	rm -f edits.el

.PHONY: all clean
