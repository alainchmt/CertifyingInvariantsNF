import IdealArithmetic.MordellExamples.MordellExample17.NF2_2_17_1.PrimesBelow2_2_17_1F0

namespace NF2_2_17_1

noncomputable section
abbrev eC := ![1, 2]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 3 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB3I0

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB3 : PrimesBelowBoundCertificate O 3 := by
  refine primesBelowBoundCertificate_of_Interval O eC 2 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 2 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 2 hC

lemma cert_eq_𝔭 : PB3.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 2 rfl rfl hel hC

end

end NF2_2_17_1
