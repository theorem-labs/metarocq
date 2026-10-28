.PHONY: all bugd clean mrproper plugin-demo

all: bugs plugin-demo

bugs: Makefile.rocq
	$(MAKE) -f Makefile.rocq TIMED=$(TIMED)
	bash check_fail_messages.sh nested_positivity.v
	bash check_fail_messages.sh positivity_red.v
	bash check_fail_messages.sh template_partial.v

Makefile.rocq: Makefile _RocqProject
	rocq makefile -f _RocqProject -o Makefile.rocq

_RocqProject: _RocqProject.in metarocq-config
	cat metarocq-config > _RocqProject
	cat _RocqProject.in >> _RocqProject

clean: Makefile.rocq
	$(MAKE) -f Makefile.rocq clean

mrproper:
	rm -f Makefile.rocq

plugin-demo:
	$(MAKE) -C plugin-demo

vos: Makefile.rocq
	$(MAKE) -f Makefile.rocq vos

quick: Makefile.rocq
	$(MAKE) -f Makefile.rocq COQEXTRAFLAGS="-unset \"Universe Checking\"" vos

TEST_SUITE_BLACKLIST := \
	TypeAnnotationTests.v \
	CheckerTest.v \
	ErasureTests.v \
	self_erasure.v \
	primitive.v \
	plugin-demo/.*.v \
	nested_positivity_stdlib.v \
	#

space := $(subst ,, )

TEST_SUITE_BLACKLIST_SED:=\($(subst $(space),\|,$(strip $(TEST_SUITE_BLACKLIST)))\)

.PHONY: update-_RocqProject.in
update-_RocqProject.in:
	{ printf '%s\n\n%s\n\n' '-R . MetaRocq.TestSuite' '# list obtained with `git ls-files "*.v"`'; \
	  { git ls-files "*.v" || ls -1 *.v; } | env LC_COLLATE=C sort | sed 's,^$(TEST_SUITE_BLACKLIST_SED)$$,# \1,g'; \
	} > _RocqProject.in
