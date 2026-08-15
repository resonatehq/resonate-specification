package model

import (
	"strings"
	"testing"
)

// The corpus is generated, so what needs testing is the generator's
// contract, not the files. Three properties, each of which has been wrong
// at least once while this was being written.

// Every case must actually exercise the behaviour it is named for.
// Minimization is the reason this can fail: it removes steps while the
// witness still holds, and an off-by-one in the containment check produces
// cases that no longer witness anything.
func TestEveryCaseWitnessesItsBucket(t *testing.T) {
	c := BuildCorpus(Materialized, 40)
	if len(c.Cases) == 0 {
		t.Fatal("empty corpus")
	}
	for _, cs := range c.Cases {
		got := bucketsOf(Materialized, cs.script)
		if !containsStr(got, cs.Witness) {
			t.Errorf("case %q does not reach its own witness %q; reaches %v",
				cs.Name, cs.Witness, got)
		}
	}
}

// The observational file must be exactly the driven file with its τ rows
// removed. If these two ever disagree, an implementor replaying the two
// tiers is running two different tests and only one of them is the spec's.
func TestObservationalIsTheTauErasureOfDriven(t *testing.T) {
	c := BuildCorpus(Materialized, 40)
	for _, cs := range c.Cases {
		var erased []string
		for _, line := range strings.Split(strings.TrimRight(cs.Driven(Materialized), "\n"), "\n") {
			if line != "" && !strings.HasPrefix(line, `{"kind":"tau.`) {
				erased = append(erased, line)
			}
		}
		want := strings.TrimRight(cs.Observational(Materialized), "\n")
		got := strings.Join(erased, "\n")
		if got != want {
			t.Errorf("case %q: τ-erasure of the driven trace is not the observational trace\n got: %s\nwant: %s",
				cs.Name, got, want)
		}
	}
}

// A case with no external events is driven-tier only, and must be marked
// so. An unmarked one would be written out as a zero-byte trace that every
// checker rejects as a parse error — which reads as a broken corpus rather
// than as the real fact, that a silent τ no-op has no observational
// projection at all.
func TestDrivenOnlyCasesAreMarked(t *testing.T) {
	c := BuildCorpus(Materialized, 40)
	for _, cs := range c.Cases {
		empty := cs.Observational(Materialized) == ""
		if empty && cs.Tier != "driven" {
			t.Errorf("case %q has no external events but is tier %q", cs.Name, cs.Tier)
		}
		if !empty && cs.Tier != "both" {
			t.Errorf("case %q has external events but is tier %q", cs.Name, cs.Tier)
		}
	}
}
