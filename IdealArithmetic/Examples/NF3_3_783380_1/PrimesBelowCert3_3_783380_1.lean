import IdealArithmetic.Examples.NF3_3_783380_1.PrimesBelow3_3_783380_1F0
import IdealArithmetic.Examples.NF3_3_783380_1.PrimesBelow3_3_783380_1F1
import IdealArithmetic.Examples.NF3_3_783380_1.PrimesBelow3_3_783380_1F2
import IdealArithmetic.Examples.NF3_3_783380_1.PrimesBelow3_3_783380_1F3

noncomputable section
abbrev eC := ![1, 31, 79, 137, 196]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 197 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB197I0
  exact PB197I1
  exact PB197I2
  exact PB197I3

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB197 : PrimesBelowBoundCertificate O 197 := by
  refine primesBelowBoundCertificate_of_Interval O eC 196 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 196 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 196 hC

lemma cert_eq_𝔭 : PB197.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 196 rfl rfl hel hC
