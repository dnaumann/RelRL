# This makefile will run the makefile in all the examples in this directory
# including subdirectories. Each example should have its own makefile that can
# be run independently.


EXAMPLES := $(wildcard */Makefile)

all: $(EXAMPLES)
	@for example in $(EXAMPLES); do \
		$(MAKE) -C $$(dirname $$example); \
	done

clean: $(EXAMPLES)
	@for example in $(EXAMPLES); do \
		$(MAKE) -C $$(dirname $$example) clean; \
	done	
