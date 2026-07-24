
import IdealArithmetic.Examples.NF3_1_334235_1.RI3_1_334235_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![493040469, -15418624, -8708877]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![493040469, -15418624, -8708877]] 
 ![![139, 0, 0], ![0, 139, 0], ![85, 75, 1]] where
  M :=![![![493040469, -15418624, -8708877], ![1846281924, 14052234, -24127501], ![5115030212, 519269369, -10075267]]]
  hmulB := by decide  
  f := ![![![-89115771297269, 33651797252239, -3556777291078]], ![![754036785708536, -284738522306559, 30095019961161]], ![![306458806734577, -115724629661721, 12231344784173]]]
  g := ![![![8872626, 4588109, -8708877], ![28036831, 13119531, -24127501], ![42959913, 9172046, -10075267]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [101, 98, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 138], [0, 1]]
 g := ![![[34, 64], [9, 100], [125], [129, 96], [113], [13], [1]], ![[17, 75], [78, 39], [125], [34, 43], [113], [13], [1]]]
 h' := ![![[41, 138], [64, 8], [3, 129], [37, 79], [49, 42], [131, 35], [38, 41], [0, 1]], ![[0, 1], [114, 131], [10, 10], [79, 60], [103, 97], [37, 104], [51, 98], [41, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64]]
 b := ![[], [39, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [101, 98, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-535, -145, -39]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![20, 20, -39]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89115771297269, -33651797252239, 3556777291078]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![89115771297269, -33651797252239, 3556777291078]] 
 ![![139, 0, 0], ![63, 1, 0], ![62, 0, 1]] where
  M :=![![![89115771297269, -33651797252239, 3556777291078], ![-754036785708536, 284738522306559, -30095019961161], ![6380144231766132, -2409262883572391, 254643502345398]]]
  hmulB := by decide  
  f := ![![![-493040469, 15418624, 8708877]], ![![-236746989, 6887202, 4120768]], ![![-256716110, 3141621, 3957019]]]
  g := ![![![14306897885910, -33651797252239, 3556777291078], ![-121055197506689, 284738522306559, -30095019961161], ![1024286393895051, -2409262883572391, 254643502345398]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![493040469, -15418624, -8708877]] ![![89115771297269, -33651797252239, 3556777291078]]
  ![![139, 0, 0]] where
 M := ![![![-139, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0)
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0]] 
 ![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [46, 5, 119, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [84, 124, 17], [95, 24, 132], [0, 1]]
 g := ![![[50, 128, 102], [89, 5], [118, 82, 121], [105, 144], [57, 85, 1], [30, 1], []], ![[41, 14, 43, 129], [138, 16], [118, 32, 89, 73], [64, 9], [136, 131, 137, 102], [52, 129], [72, 140]], ![[49, 6, 25, 118], [54, 118], [40, 59, 52, 110], [116, 76], [75, 105, 61, 7], [84, 29], [106, 140]]]
 h' := ![![[84, 124, 17], [2, 31, 20], [85, 62, 68], [111, 69, 11], [60, 8, 137], [110, 102, 1], [0, 0, 1], [0, 1]], ![[95, 24, 132], [6, 43, 113], [29, 69, 4], [7, 51, 96], [57, 84, 146], [55, 9, 119], [19, 26, 24], [84, 124, 17]], ![[0, 1], [103, 75, 16], [90, 18, 77], [6, 29, 42], [53, 57, 15], [92, 38, 29], [126, 123, 124], [95, 24, 132]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83, 51], []]
 b := ![[], [6, 63, 146], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [46, 5, 119, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1287211, -871501, 139017]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8639, -5849, 933]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 3307949 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def PBC149 : ContainsPrimesAboveP 149 ![I149N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![149, 0, 0]]) timesTableT_eq_Table B_one_repr 149 (by decide) 𝕀

instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13798948953123481, -5210743572150820, 550741889597697]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![13798948953123481, -5210743572150820, 550741889597697]] 
 ![![151, 0, 0], ![0, 151, 0], ![43, 124, 1]] where
  M :=![![![13798948953123481, -5210743572150820, 550741889597697], ![-116757280594711764, 44089752880996816, -4660001682553123], ![987920356701262076, -373057373135133529, 39429751198443693]]]
  hmulB := by decide  
  f := ![![![-43395229, -36504003, -3708092]], ![![786115504, -247340289, -40212095]], ![![689650939, -222949786, -35982120]]]
  g := ![![![-65450015228990, -486773098558048, 550741889597697], ![553793322881275, 4118741467003868, -4660001682553123], ![-4685820826700773, -34849976965179811, 39429751198443693]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [8, 140, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 150], [0, 1]]
 g := ![![[93, 19], [88, 1], [99, 17], [39], [34, 91], [121], [1]], ![[0, 132], [99, 150], [135, 134], [39], [129, 60], [121], [1]]]
 h' := ![![[11, 150], [51, 64], [114, 1], [135, 116], [30, 103], [2, 98], [143, 11], [0, 1]], ![[0, 1], [0, 87], [125, 150], [52, 35], [106, 48], [23, 53], [113, 140], [11, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [78]]
 b := ![[], [12, 39]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [8, 140, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4644, -255, 43]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-43, -37, 43]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43395229, 36504003, 3708092]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![43395229, 36504003, 3708092]] 
 ![![151, 0, 0], ![26, 1, 0], ![79, 0, 1]] where
  M :=![![![43395229, 36504003, 3708092], ![-786115504, 247340289, 40212095], ![-8524964140, 1425549721, 287552384]]]
  hmulB := by decide  
  f := ![![![-13798948953123481, 5210743572150820, -550741889597697]], ![![-1602750941632442, 605229006588904, -63968791039649]], ![![-13761836582768325, 5196729240629459, -549260665408356]]]
  g := ![![![-7938067, 36504003, 3708092], ![-68832573, 247340289, 40212095], ![-452356922, 1425549721, 287552384]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![13798948953123481, -5210743572150820, 550741889597697]] ![![43395229, 36504003, 3708092]]
  ![![151, 0, 0]] where
 M := ![![![-151, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0)
instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-55, 0, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![-55, 0, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![102, 0, 1]] where
  M :=![![![-55, 0, 1], ![-212, 0, 1], ![-212, -157, 1]]]
  hmulB := by decide  
  f := ![![![1, -1, 0]], ![![0, 1, -1]], ![![2, -1, 0]]]
  g := ![![![-1, 0, 1], ![-2, 0, 1], ![-2, -1, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [151, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [143, 156], [0, 1]]
 g := ![![[50, 46], [48], [32, 14], [42, 42], [108, 17], [39], [1]], ![[34, 111], [48], [150, 143], [82, 115], [27, 140], [39], [1]]]
 h' := ![![[143, 156], [100, 49], [35, 26], [95, 64], [20, 55], [113, 71], [6, 143], [0, 1]], ![[0, 1], [42, 108], [142, 131], [141, 93], [35, 102], [61, 86], [45, 14], [143, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [137]]
 b := ![[], [87, 147]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [151, 14, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-470, -1727, 451]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-296, -11, 451]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![-1, 1, 0]] 
 ![![157, 0, 0], ![156, 1, 0], ![156, 0, 1]] where
  M :=![![![-1, 1, 0], ![0, -1, 1], ![-212, 55, 0]]]
  hmulB := by decide  
  f := ![![![55, 0, -1]], ![![56, 0, -1]], ![![56, 1, -1]]]
  g := ![![![-1, 1, 0], ![0, -1, 1], ![-56, 55, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![-55, 0, 1]] ![![-1, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![-157, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0)
instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4649, 229, 92]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![-4649, 229, 92]] 
 ![![163, 0, 0], ![0, 163, 0], ![54, 146, 1]] where
  M :=![![![-4649, 229, 92], ![-19504, 411, 321], ![-68052, -1849, 732]]]
  hmulB := by decide  
  f := ![![![-5487, 2072, -219]], ![![46428, -17532, 1853]], ![![37358, -14107, 1491]]]
  g := ![![![-59, -81, 92], ![-226, -285, 321], ![-660, -667, 732]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [139, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [128, 162], [0, 1]]
 g := ![![[114, 158], [64, 155], [113], [25], [144], [107, 84], [1]], ![[126, 5], [18, 8], [113], [25], [144], [101, 79], [1]]]
 h' := ![![[128, 162], [69, 22], [160, 36], [120, 73], [3, 158], [123, 151], [24, 128], [0, 1]], ![[0, 1], [114, 141], [41, 127], [10, 90], [15, 5], [54, 12], [108, 35], [128, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [134]]
 b := ![[], [113, 67]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [139, 35, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-497, -82, 24]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11, -22, 24]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5487, -2072, 219]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![5487, -2072, 219]] 
 ![![163, 0, 0], ![16, 1, 0], ![70, 0, 1]] where
  M :=![![![5487, -2072, 219], ![-46428, 17532, -1853], ![392836, -148343, 15679]]]
  hmulB := by decide  
  f := ![![![4649, -229, -92]], ![![576, -25, -11]], ![![2414, -87, -44]]]
  g := ![![![143, -2072, 219], ![-1210, 17532, -1853], ![10238, -148343, 15679]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![-4649, 229, 92]] ![![5487, -2072, 219]]
  ![![163, 0, 0]] where
 M := ![![![-163, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC163 : ContainsPrimesAboveP 163 ![I163N0, I163N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
    exact isPrimeI163N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 163 (by decide) (𝕀 ⊙ MulI163N0)


lemma PB164I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 163 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 163 (by omega)

def PB164I3 : PrimesBelowBoundCertificateInterval O 137 163 164 where
  m := 5
  g := ![2, 1, 2, 2, 2]
  P := ![139, 149, 151, 157, 163]
  hP := PB164I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC139
    · exact PBC149
    · exact PBC151
    · exact PBC157
    · exact PBC163
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![19321, 139]
    · exact ![3307949]
    · exact ![22801, 151]
    · exact ![24649, 157]
    · exact ![26569, 163]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
  β := ![I139N1, I151N1, I157N1, I163N1]
  Il := ![[I139N1], [], [I151N1], [I157N1], [I163N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
