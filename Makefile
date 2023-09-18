# Always run with nproc jobs by default. Can be overridden by the user.
MAKEFLAGS := --jobs=$(shell nproc)

# Comment out the below line if you want to be quiet by default.
VERBOSE ?= 1
ifeq ($(V),1)
E=@true
Q=
else
E=@echo
Q=@
MAKEFLAGS += -s
endif

# Collect all Coq files in the current directory and its subdirectories.
SRCS := $(shell egrep "^.*\.v$$" _CoqProject)
# Replace .v with .aux to get the auxiliary files.
AUXS := $(join $(dir $(SRCS)), $(addprefix ., $(notdir $(SRCS:.v=.aux))))

.PHONY: help clean coq install make-pretty-timed-after make-pretty-timed-before pretty-timed print-pretty-timed-diff uninstall
.DEFAULT_GOAL=help

coq: Makefile.coq ## Compile the Coq files
	$(E) "MAKE Makefile.coq"
	$(Q)$(MAKE) -f Makefile.coq

# Generate a Makefile.coq for the coq sources using coq_makefile.
Makefile.coq: _CoqProject Makefile $(SRCS)
	$(E) "COQ_MAKEFILE Makefile.coq"
	$(Q)coq_makefile -f _CoqProject -o Makefile.coq

# Clean up using the generated Makefile.coq and do some cleaning ourselves.
clean: Makefile.coq
	$(Q)$(MAKE) -f Makefile.coq clean
	$(Q)rm -f $(AUXS)
	$(Q)rm -f Makefile.coq *.bak *.d *.glob *~ result*

# Targets which are passed through to Makefile.coq.
install uninstall pretty-timed make-pretty-timed-before make-pretty-timed-after print-pretty-timed-diff: Makefile.coq
	$(Q)$(MAKE) -f Makefile.coq $@

help:
	@grep -E '(^[a-zA-Z_-]+:.*?##.*$$)|(^##)' $(MAKEFILE_LIST) | awk 'BEGIN {FS = ":.*?## "}; {printf "\033[32m%-10s\033[0m %s\n", $$1, $$2}' | sed -e 's/\[32m##/[33m/'
