import IdealArithmetic.Examples.NF3_1_378695_1.PrimesBelow3_1_378695_1F0
import IdealArithmetic.Examples.NF3_1_378695_1.PrimesBelow3_1_378695_1F1
import IdealArithmetic.Examples.NF3_1_378695_1.PrimesBelow3_1_378695_1F2
import IdealArithmetic.Examples.NF3_1_378695_1.PrimesBelow3_1_378695_1F3

noncomputable section
abbrev eC := ![1, 31, 79, 137, 174]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 175 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB175I0
  exact PB175I1
  exact PB175I2
  exact PB175I3

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB175 : PrimesBelowBoundCertificate O 175 := by
  refine primesBelowBoundCertificate_of_Interval O eC 174 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 174 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 174 hC

lemma cert_eq_𝔭 : PB175.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 174 rfl rfl hel hC
