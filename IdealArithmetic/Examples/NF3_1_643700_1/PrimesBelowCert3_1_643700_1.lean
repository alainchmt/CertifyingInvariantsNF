import IdealArithmetic.Examples.NF3_1_643700_1.PrimesBelow3_1_643700_1F0
import IdealArithmetic.Examples.NF3_1_643700_1.PrimesBelow3_1_643700_1F1
import IdealArithmetic.Examples.NF3_1_643700_1.PrimesBelow3_1_643700_1F2
import IdealArithmetic.Examples.NF3_1_643700_1.PrimesBelow3_1_643700_1F3
import IdealArithmetic.Examples.NF3_1_643700_1.PrimesBelow3_1_643700_1F4

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 227]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 228 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB228I0
  exact PB228I1
  exact PB228I2
  exact PB228I3
  exact PB228I4

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB228 : PrimesBelowBoundCertificate O 228 := by
  refine primesBelowBoundCertificate_of_Interval O eC 227 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 227 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 227 hC

lemma cert_eq_𝔭 : PB228.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 227 rfl rfl hel hC
