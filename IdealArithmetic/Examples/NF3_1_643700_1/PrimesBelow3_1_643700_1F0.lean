
import IdealArithmetic.Examples.NF3_1_643700_1.RI3_1_643700_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-13, 0, 1]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0], ![-13, 0, 1]] 
 ![![2, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![-13, 0, 1], ![-183, 6, 3], ![-143, -21, 8]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![7, 11, 1], ![-10, 0, 1]], ![![7, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![-1, 2, 0], ![-1, 0, 2]], ![![-7, 0, 1], ![-96, 6, 3], ![-65, -21, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-52, 2, 3]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-52, 2, 3]] 
 ![![2, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![-52, 2, 3], ![-543, 1, 21], ![-795, -25, 17]]]
  hmulB := by decide  
  f := ![![![-542, 109, -39]], ![![3461, -696, 249]], ![![-7185, 1445, -517]]]
  g := ![![![-27, 2, 3], ![-272, 1, 21], ![-385, -25, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![-13, 0, 1]] ![![2, 0, 0], ![-13, 0, 1]]
  ![![542, -109, 39]] where
 M := ![![![4, 0, 0], ![-26, 0, 2]], ![![-26, 0, 2], ![26, -21, -5]]]
 hmul := by decide  
 g := ![![![![104, -4, -6]], ![![119, 51, 22]]], ![![![119, 51, 22]], ![![-7013, -78, 224]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![542, -109, 39]] ![![-52, 2, 3]]
  ![![2, 0, 0]] where
 M := ![![![-2, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N0, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N0
    exact isPrimeI2N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-390163777878136, 78463913188217, -28072505677328]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-390163777878136, 78463913188217, -28072505677328]] 
 ![![3, 0, 0], ![0, 1, 0], ![2, 0, 1]] where
  M :=![![![-390163777878136, 78463913188217, -28072505677328], ![5372660278515675, -1080469212123802, 386565962097318], ![-10344527801585807, 2080336969800011, -744294657537373]]]
  hmulB := by decide  
  f := ![![![61618352, -3883333, -4340950]], ![![260914617, -4364344, -12107616]], ![![484880831, 3203319, -16624499]]]
  g := ![![![-111339588841160, 78463913188217, -28072505677328], ![1533176118107013, -1080469212123802, 386565962097318], ![-2951979495503687, 2080336969800011, -744294657537373]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-14, 0, 1]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3, 0, 0], ![-14, 0, 1]] 
 ![![3, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![-14, 0, 1], ![-183, 5, 3], ![-143, -21, 7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![9, 2, -4], ![15, -1, 0]], ![![5, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 3, 0], ![-1, 0, 3]], ![![-5, 0, 1], ![-62, 5, 3], ![-50, -21, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1

def I3N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-1, 1, 0]] i)))

def SI3N2: IdealEqSpanCertificate' Table ![![3, 0, 0], ![-1, 1, 0]] 
 ![![3, 0, 0], ![2, 1, 0], ![2, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![-1, 1, 0], ![3, -3, 6], ![-183, 19, 2]]]
  hmulB := by decide  
  f := ![![![660, -3, -8], ![-219, 0, 12]], ![![330, -1, -4], ![-110, 0, 6]], ![![440, -2, -5], ![-146, 0, 8]]]
  g := ![![![1, 0, 0], ![-2, 3, 0], ![-2, 0, 3]], ![![-1, 1, 0], ![-1, -3, 6], ![-75, 19, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N2 : Nat.card (O ⧸ I3N2) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N2)

lemma isPrimeI3N2 : Ideal.IsPrime I3N2 := prime_ideal_of_norm_prime hp3.out _ NI3N2
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-390163777878136, 78463913188217, -28072505677328]] ![![3, 0, 0], ![-14, 0, 1]]
  ![![3, 0, 0], ![0, 1, 0]] where
 M := ![![![-1170491333634408, 235391739564651, -84217517031984], ![-4882234911291903, 981842185164973, -351279578054781]]]
 hmul := by decide  
 g := ![![![![-390163777878136, 70617521869395, -28072505677328], ![23539173956466, 0, 0]], ![![-1627411637097301, 294552655549491, -117093192684927], ![98184218516500, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![0, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![3, 0, 0]] where
 M := ![![![9, 0, 0], ![-3, 3, 0]], ![![0, 3, 0], ![3, -3, 6]]]
 hmul := by decide  
 g := ![![![![3, 0, 0]], ![![-1, 1, 0]]], ![![![0, 1, 0]], ![![1, -1, 2]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1, I3N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-967505961476952745081787555478369027, 194570352438306465947900020012221306, -69612604081595989620894206739873988]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-967505961476952745081787555478369027, 194570352438306465947900020012221306, -69612604081595989620894206739873988]] 
 ![![5, 0, 0], ![3, 1, 0], ![0, 0, 1]] where
  M :=![![![-967505961476952745081787555478369027, 194570352438306465947900020012221306, -69612604081595989620894206739873988], ![13322817604246985498467339893433603722, -2679286143903889479774577523560417411, 958584302385050826824717499853705872], ![-25651772112541856752677832098434518714, 5158701382041338635048878721769558562, -1845659589875549129276865836979058857]]]
  hmulB := by decide  
  f := ![![![5496779376370716837, -118666851616921986, -268953879874503764]], ![![13070579518259114673, 53597761427644667, -465144877789710900]], ![![12035287733590152338, 678672259328612262, -101450531168925633]]]
  g := ![![![-310243403758374428585097523103006589, 194570352438306465947900020012221306, -69612604081595989620894206739873988], ![4272135207191730787558214492822971191, -2679286143903889479774577523560417411, 958584302385050826824717499853705872], ![-8225575251733174531564893652748638880, 5158701382041338635048878721769558562, -1845659589875549129276865836979058857]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-967505961476952745081787555478369027, 194570352438306465947900020012221306, -69612604081595989620894206739873988]] ![![-967505961476952745081787555478369027, 194570352438306465947900020012221306, -69612604081595989620894206739873988]]
  ![![5313979758284753971754416432322911406683875825915020779824815799550039093, -1068668262096409887960840629163266381726851263320882630162053437193933284, 382343865299173881323703666492150951728474389981348332697830927453190224]] where
 M := ![![![5313979758284753971754416432322911406683875825915020779824815799550039093, -1068668262096409887960840629163266381726851263320882630162053437193933284, 382343865299173881323703666492150951728474389981348332697830927453190224]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![5313979758284753971754416432322911406683875825915020779824815799550039093, -1068668262096409887960840629163266381726851263320882630162053437193933284, 382343865299173881323703666492150951728474389981348332697830927453190224]] ![![-967505961476952745081787555478369027, 194570352438306465947900020012221306, -69612604081595989620894206739873988]]
  ![![5, 0, 0]] where
 M := ![![![-29186777131949245710883733836719386024440907886950417109801353270686954060456834530382812533293145636822307495, 5869608807818128045383384268464220568020270924958317828646182109765281855191664152337852754568095173087421070, -2100005211133328927944693876624161483683345709071024118434229281815411516400889733364399047205629556333870500]]]
 hmul := by decide  
 g := ![![![![-5837355426389849142176746767343877204888181577390083421960270654137390812091366906076562506658629127364461499, 1173921761563625609076676853692844113604054184991663565729236421953056371038332830467570550913619034617484214, -420001042226665785588938775324832296736669141814204823686845856363082303280177946672879809441125911266774100]]]]
 hle2 := by decide  

def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N0, I5N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-12, 0, 1]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0], ![-12, 0, 1]] 
 ![![7, 0, 0], ![0, 7, 0], ![2, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![-12, 0, 1], ![-183, 7, 3], ![-143, -21, 9]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, 0, 7]], ![![-2, 0, 1], ![-27, 1, 3], ![-23, -3, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [6, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 6], [0, 1]]
 g := ![![[3, 2], [3, 1]], ![[2, 5], [6, 6]]]
 h' := ![![[3, 6], [3, 3], [0, 1]], ![[0, 1], [5, 4], [3, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [4, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [6, 4, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3282, -3276, 2034]
  a := ![-5, 3, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1050, -468, 2034]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-3, 1, 0]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![7, 0, 0], ![-3, 1, 0]] 
 ![![7, 0, 0], ![4, 1, 0], ![5, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![-3, 1, 0], ![3, -5, 6], ![-183, 19, 0]]]
  hmulB := by decide  
  f := ![![![25, -48, 60], ![-14, -70, 0]], ![![13, -24, 30], ![-6, -35, 0]], ![![17, -34, 43], ![-12, -50, 0]]]
  g := ![![![1, 0, 0], ![-4, 7, 0], ![-5, 0, 7]], ![![-1, 1, 0], ![-1, -5, 6], ![-37, 19, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![-12, 0, 1]] ![![7, 0, 0], ![-3, 1, 0]]
  ![![7, 0, 0]] where
 M := ![![![49, 0, 0], ![-21, 7, 0]], ![![-84, 0, 7], ![-147, 7, 0]]]
 hmul := by decide  
 g := ![![![![7, 0, 0]], ![![-3, 1, 0]]], ![![![-12, 0, 1]], ![![-21, 1, 0]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0]] 
 ![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [3, 9, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 6, 9], [1, 4, 2], [0, 1]]
 g := ![![[4, 9, 9], [2, 0, 1], []], ![[2, 7, 7, 3], [5, 9, 5, 1], [9, 4]], ![[9, 3, 7, 2], [8, 6, 2, 6], [5, 4]]]
 h' := ![![[10, 6, 9], [5, 4, 8], [0, 0, 1], [0, 1]], ![[1, 4, 2], [2, 9, 2], [7, 5, 4], [10, 6, 9]], ![[0, 1], [7, 9, 1], [8, 6, 6], [1, 4, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 1], []]
 b := ![[], [0, 6, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [3, 9, 0, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1953897, -470514, 140338]
  a := ![3, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![177627, -42774, 12758]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def PBC11 : ContainsPrimesAboveP 11 ![I11N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![11, 0, 0]]) timesTableT_eq_Table B_one_repr 11 (by decide) 𝕀

instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-957936, 112331, 94472]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-957936, 112331, 94472]] 
 ![![13, 0, 0], ![0, 13, 0], ![8, 11, 1]] where
  M :=![![![-957936, 112331, 94472], ![-16951383, 612370, 957402], ![-34066069, 150377, 1362969]]]
  hmulB := by decide  
  f := ![![![-53128468152, 10684404215, -3822623494]], ![![731593312047, -147127122968, 52638554808]], ![![477991375046, -96126488113, 34391751235]]]
  g := ![![![-131824, -71297, 94472], ![-1893123, -763004, 957402], ![-3459217, -1141714, 1362969]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [11, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 12], [0, 1]]
 g := ![![[3, 12], [1], [6, 1]], ![[10, 1], [1], [12, 12]]]
 h' := ![![[6, 12], [3, 8], [12, 12], [0, 1]], ![[0, 1], [12, 5], [6, 1], [6, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [9, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [11, 7, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-738264, -1294301, 788740]
  a := ![-129, 65, -194]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-542168, -766957, 788740]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53128468152, -10684404215, 3822623494]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![53128468152, -10684404215, 3822623494]] 
 ![![13, 0, 0], ![9, 1, 0], ![3, 0, 1]] where
  M :=![![![53128468152, -10684404215, 3822623494], ![-731593312047, 147127122968, -52638554808], ![1408610811703, -283278773459, 101350348881]]]
  hmulB := by decide  
  f := ![![![957936, -112331, -94472]], ![![1967139, -124873, -139050]], ![![2841529, -37490, -126645]]]
  g := ![![![10601556585, -10684404215, 3822623494], ![-145986288795, 147127122968, -52638554808], ![281082209707, -283278773459, 101350348881]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-957936, 112331, 94472]] ![![53128468152, -10684404215, 3822623494]]
  ![![13, 0, 0]] where
 M := ![![![-13, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0)
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![-18, 3, 1]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0], ![-18, 3, 1]] 
 ![![17, 0, 0], ![0, 17, 0], ![16, 3, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![-18, 3, 1], ![-174, -5, 21], ![-692, 36, 12]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-16, -3, 17]], ![![-2, 0, 1], ![-30, -4, 21], ![-52, 0, 12]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [13, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 16], [0, 1]]
 g := ![![[11, 4], [13], [15], [1]], ![[0, 13], [13], [15], [1]]]
 h' := ![![[10, 16], [14, 2], [8, 9], [4, 10], [0, 1]], ![[0, 1], [0, 15], [13, 8], [2, 7], [10, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [8, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [13, 7, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1148, -4257, 2406]
  a := ![-5, 4, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2332, -675, 2406]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![-4, 1, 0]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![17, 0, 0], ![-4, 1, 0]] 
 ![![17, 0, 0], ![13, 1, 0], ![5, 0, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![-4, 1, 0], ![3, -6, 6], ![-183, 19, -1]]]
  hmulB := by decide  
  f := ![![![181, -381, 384], ![-51, -1088, 0]], ![![137, -286, 288], ![-33, -816, 0]], ![![53, -112, 113], ![-16, -320, 0]]]
  g := ![![![1, 0, 0], ![-13, 17, 0], ![-5, 0, 17]], ![![-1, 1, 0], ![3, -6, 6], ![-25, 19, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![17, 0, 0], ![-18, 3, 1]] ![![17, 0, 0], ![-4, 1, 0]]
  ![![17, 0, 0]] where
 M := ![![![289, 0, 0], ![-68, 17, 0]], ![![-306, 51, 17], ![-102, -17, 17]]]
 hmul := by decide  
 g := ![![![![17, 0, 0]], ![![-4, 1, 0]]], ![![![-18, 3, 1]], ![![-6, -1, 1]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0)
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0]] 
 ![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [5, 6, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 8, 18], [12, 10, 1], [0, 1]]
 g := ![![[5, 5, 4], [18, 14, 7], [6, 1], []], ![[5, 17, 14, 18], [15, 18, 2, 18], [8, 5], [9, 1]], ![[8, 12, 13, 9], [12, 3, 1, 5], [14, 7], [7, 1]]]
 h' := ![![[13, 8, 18], [5, 0, 17], [8, 16, 11], [0, 0, 1], [0, 1]], ![[12, 10, 1], [4, 6, 18], [3, 0, 18], [10, 16, 10], [13, 8, 18]], ![[0, 1], [15, 13, 3], [12, 3, 9], [14, 3, 8], [12, 10, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 7], []]
 b := ![[], [1, 16, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [5, 6, 13, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4245607, 1162116, -328206]
  a := ![-5, 3, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-223453, 61164, -17274]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 6859 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def PBC19 : ContainsPrimesAboveP 19 ![I19N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![19, 0, 0]]) timesTableT_eq_Table B_one_repr 19 (by decide) 𝕀

instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0]] 
 ![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [17, 13, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 22, 1], [20, 0, 22], [0, 1]]
 g := ![![[10, 2, 6], [3, 20, 3], [16, 11, 1], []], ![[19, 21, 11, 2], [5, 0, 3, 16], [16, 1], [9, 1]], ![[18, 0, 12, 10], [17, 10, 19, 17], [6, 14, 14, 22], [11, 1]]]
 h' := ![![[14, 22, 1], [18, 5, 12], [4, 19, 16], [0, 0, 1], [0, 1]], ![[20, 0, 22], [6, 6, 5], [15, 11, 19], [20, 22], [14, 22, 1]], ![[0, 1], [6, 12, 6], [20, 16, 11], [6, 1, 22], [20, 0, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 5], []]
 b := ![[], [12, 21, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [17, 13, 12, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2280606400, -711189785, 210258686]
  a := ![43, -22, 85]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![99156800, -30921295, 9141682]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def PBC23 : ContainsPrimesAboveP 23 ![I23N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![23, 0, 0]]) timesTableT_eq_Table B_one_repr 23 (by decide) 𝕀

instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0]] 
 ![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [14, 4, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 1, 13], [1, 27, 16], [0, 1]]
 g := ![![[12, 11, 4], [3, 7], [9, 26, 20], [1]], ![[5, 15, 25, 4], [4, 1], [28, 0, 9, 20], [20, 22, 23, 22]], ![[18, 4, 1, 9], [17, 20], [17, 7, 5, 16], [8, 6, 21, 7]]]
 h' := ![![[6, 1, 13], [0, 26, 27], [19, 28, 23], [15, 25, 7], [0, 1]], ![[1, 27, 16], [6, 22, 23], [27, 16, 28], [23, 10, 21], [6, 1, 13]], ![[0, 1], [7, 10, 8], [19, 14, 7], [5, 23, 1], [1, 27, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 4], []]
 b := ![[], [8, 15, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [14, 4, 22, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9454, -27405, 11223]
  a := ![1, 0, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-326, -945, 387]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 24389 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def PBC29 : ContainsPrimesAboveP 29 ![I29N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![29, 0, 0]]) timesTableT_eq_Table B_one_repr 29 (by decide) 𝕀

instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11635224499380109758747960, 2339902617330936415627827, -837161018873089131875090]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-11635224499380109758747960, 2339902617330936415627827, -837161018873089131875090]] 
 ![![31, 0, 0], ![0, 31, 0], ![4, 4, 1]] where
  M :=![![![-11635224499380109758747960, 2339902617330936415627827, -837161018873089131875090], ![160220174305768120380024951, -32221089092630676095630324, 11527932647366351098141692], ![-308488153272709618201754471, 62038531125622663666305603, -22195898043722172281241369]]]
  hmulB := by decide  
  f := ![![![-4889257166880, -384474091803, -15277414004]], ![![1642344487323, -4410579849350, -2352676792830]], ![![1921154138203, -844012832735, -510816837539]]]
  g := ![![![-267309045931863007459600, 183501506220106223971877, -837161018873089131875090], ![3680917539235571483466393, -2526865151035357435103132, 11527932647366351098141692], ![-7087243906381320292799645, 4865229783887462993266809, -22195898043722172281241369]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [18, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 30], [0, 1]]
 g := ![![[3, 19], [4, 4], [22, 8], [8, 1]], ![[0, 12], [5, 27], [24, 23], [16, 30]]]
 h' := ![![[8, 30], [21, 9], [7, 29], [11, 15], [0, 1]], ![[0, 1], [0, 22], [22, 2], [7, 16], [8, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [30, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [18, 23, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6987, -8661, 5670]
  a := ![8, -5, 16]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-957, -1011, 5670]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4889257166880, 384474091803, 15277414004]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![4889257166880, 384474091803, 15277414004]] 
 ![![31, 0, 0], ![4, 1, 0], ![25, 0, 1]] where
  M :=![![![4889257166880, 384474091803, 15277414004], ![-1642344487323, 4410579849350, 2352676792830], ![-72543429002521, 6984182050173, 6363505136373]]]
  hmulB := by decide  
  f := ![![![11635224499380109758747960, -2339902617330936415627827, 837161018873089131875090]], ![![-3667073429298312301452681, 737467052364739691390936, -263848018447548211956172]], ![![19334476314748785876466241, -3888261179319228195387138, 1391126565017722599294149]]]
  g := ![![![95787917728, 384474091803, 15277414004], ![-2519405925983, 4410579849350, 2352676792830], ![-8373154374598, 6984182050173, 6363505136373]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-11635224499380109758747960, 2339902617330936415627827, -837161018873089131875090]] ![![4889257166880, 384474091803, 15277414004]]
  ![![31, 0, 0]] where
 M := ![![![-31, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0)


lemma PB228I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB228I0 : PrimesBelowBoundCertificateInterval O 1 31 228 where
  m := 11
  g := ![3, 3, 3, 2, 1, 2, 2, 1, 1, 1, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB228I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N1]
    · exact ![I3N0, I3N1, I3N2]
    · exact ![I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1]
    · exact ![I19N0]
    · exact ![I23N0]
    · exact ![I29N0]
    · exact ![I31N0, I31N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC2
    · exact PBC3
    · exact PBC5
    · exact PBC7
    · exact PBC11
    · exact PBC13
    · exact PBC17
    · exact PBC19
    · exact PBC23
    · exact PBC29
    · exact PBC31
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2, 2, 2]
    · exact ![3, 3, 3]
    · exact ![5, 5, 5]
    · exact ![49, 7]
    · exact ![1331]
    · exact ![169, 13]
    · exact ![289, 17]
    · exact ![6859]
    · exact ![12167]
    · exact ![24389]
    · exact ![961, 31]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N0
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N1
      exact NI3N2
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N0
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I2N1, I3N0, I3N1, I3N2, I5N0, I7N0, I7N1, I13N0, I13N1, I17N1, I31N1]
  Il := ![[I2N0, I2N0, I2N1], [I3N0, I3N1, I3N2], [I5N0, I5N0, I5N0], [I7N0, I7N1], [], [I13N0, I13N1], [I17N1], [], [], [], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
