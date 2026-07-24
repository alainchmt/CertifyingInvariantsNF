import IdealArithmetic.Examples.NF3_1_780300_1.PrimesBelow3_1_780300_1F0
import IdealArithmetic.Examples.NF3_1_780300_1.PrimesBelow3_1_780300_1F1
import IdealArithmetic.Examples.NF3_1_780300_1.PrimesBelow3_1_780300_1F2
import IdealArithmetic.Examples.NF3_1_780300_1.PrimesBelow3_1_780300_1F3
import IdealArithmetic.Examples.NF3_1_780300_1.PrimesBelow3_1_780300_1F4

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 249]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 250 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB250I0
  exact PB250I1
  exact PB250I2
  exact PB250I3
  exact PB250I4

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB250 : PrimesBelowBoundCertificate O 250 := by
  refine primesBelowBoundCertificate_of_Interval O eC 249 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 249 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 249 hC

lemma cert_eq_𝔭 : PB250.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 249 rfl rfl hel hC
