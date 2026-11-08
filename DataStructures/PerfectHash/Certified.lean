import DataStructures.PerfectHash.Total.Contract

namespace PerfectHash
open WordRam StaticSet

/-- Executable width-independent program data, defined directly rather than
recovered from an existential proof or the certificate's proof fields. -/
def fksCode : DictionaryCode := ⟨Total.program,Query.program⟩

theorem fksCode_correct : DictionarySpec fksCode Table.representation Total.bounds := Total.specification

/-- A concrete certificate containing explicit programs, retained representation,
uniform constants, and the complete original contract. -/
def certifiedFKS : CertifiedDictionary :=
  ⟨fksCode,Table.representation,Total.bounds,fksCode_correct⟩

theorem certifiedFKS_code : certifiedFKS.code = fksCode := rfl

/-- Constructive algorithm existence is a consequence of the explicit certified
value. Both arrays remain independently available as executable data. -/
theorem dictionary_algorithms_exist :
    ∃ (code : DictionaryCode) (rep : Representation) (b : ResourceBounds), DictionarySpec code rep b :=
  certifiedFKS.exists_code

/-- Public complete-build/query entry point, hiding all construction invariants. -/
theorem certified_query_after_build (ha : Admissible w xs.length l)
    (hi : BuildInput w xs.length l rs) (hm : ArrayAt mem l.inputBase xs) (rho : RandomMemory w) :
    let result := run fksCode.preprocess rho (constructionFuel Total.bounds w xs.length) (.initial rs mem)
    let retained := readDescriptor result.state.regs
    ∀ mem', AgreeOn retained result.state.mem mem' → ∀ (q : Word w) queryRegs,
      QueryInput retained q queryRegs → ∀ queryRho : RandomMemory w,
        QueryOutput xs.toFinset retained q mem' Total.bounds.query
          (run fksCode.query queryRho Total.bounds.query (.initial queryRegs mem')) :=
  fksCode_correct.query_after_build ha hi hm rho

end PerfectHash
