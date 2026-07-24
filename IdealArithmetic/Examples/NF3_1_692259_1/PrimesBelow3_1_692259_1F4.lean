
import IdealArithmetic.Examples.NF3_1_692259_1.RI3_1_692259_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0]] 
 ![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 3 2 7 [65, 175, 101, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14, 104, 117], [82, 92, 80], [0, 1]]
 g := ![![[21, 39, 65], [171, 143], [186, 196, 132], [137, 132], [24, 92], [96, 154], [1]], ![[13, 105, 107, 110], [174, 4], [189, 154, 148, 122], [10, 163], [21, 88], [79, 6], [185, 38, 99, 3]], ![[166, 166, 141, 98], [156, 136], [175, 147, 28, 159], [51, 28], [31, 137], [91, 63], [149, 84, 7, 194]]]
 h' := ![![[14, 104, 117], [124, 79, 159], [124, 83, 145], [76, 128, 59], [71, 29, 59], [152, 77, 17], [132, 22, 96], [0, 1]], ![[82, 92, 80], [157, 108, 34], [108, 46, 2], [45, 73, 113], [33, 21, 153], [77, 33, 132], [175, 106, 177], [14, 104, 117]], ![[0, 1], [151, 10, 4], [176, 68, 50], [43, 193, 25], [194, 147, 182], [150, 87, 48], [130, 69, 121], [82, 92, 80]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [153, 171], []]
 b := ![[], [134, 107, 44], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 3
  hpos := by decide
  P := [65, 175, 101, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-46098, 81558, -25413]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-234, 414, -129]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 7645373 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def PBC197 : ContainsPrimesAboveP 197 ![I197N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![197, 0, 0]]) timesTableT_eq_Table B_one_repr 197 (by decide) 𝕀

instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, -4, 0]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![23, -4, 0]] 
 ![![199, 0, 0], ![44, 1, 0], ![165, 0, 1]] where
  M :=![![![23, -4, 0], ![4, 27, -12], ![-616, 64, 19]]]
  hmulB := by decide  
  f := ![![![1281, 76, 48]], ![![320, 19, 12]], ![![1147, 68, 43]]]
  g := ![![![1, -4, 0], ![4, 27, -12], ![-33, 64, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N0 : Nat.card (O ⧸ I199N0) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N0)

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := prime_ideal_of_norm_prime hp199.out _ NI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1723, 26, -142]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![1723, 26, -142]] 
 ![![199, 0, 0], ![71, 1, 0], ![134, 0, 1]] where
  M :=![![![1723, 26, -142], ![-21894, 3969, -64], ![-11332, -6948, 3879]]]
  hmulB := by decide  
  f := ![![![-14951079, -885762, -561934]], ![![-5764717, -341525, -216666]], ![![-11057994, -655120, -415613]]]
  g := ![![![95, 26, -142], ![-1483, 3969, -64], ![-190, -6948, 3879]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1

def I199N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-176495017, -10456274, -6633538]] i)))

def SI199N2: IdealEqSpanCertificate' Table ![![-176495017, -10456274, -6633538]] 
 ![![199, 0, 0], ![84, 1, 0], ![130, 0, 1]] where
  M :=![![![-176495017, -10456274, -6633538], ![-1011108578, -59902135, -38002360], ![-2326688300, -137842364, -87448221]]]
  hmulB := by decide  
  f := ![![![127205, -15278, -3010]], ![![51442, -5491, -1516]], ![![69642, -9448, -1177]]]
  g := ![![![7860261, -10456274, -6633538], ![45030038, -59902135, -38002360], ![103619794, -137842364, -87448221]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N2 : Nat.card (O ⧸ I199N2) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N2)

lemma isPrimeI199N2 : Ideal.IsPrime I199N2 := prime_ideal_of_norm_prime hp199.out _ NI199N2
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![23, -4, 0]] ![![1723, 26, -142]]
  ![![127205, -15278, -3010]] where
 M := ![![![127205, -15278, -3010]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI199N1 : IdealMulLeCertificate' Table 
  ![![127205, -15278, -3010]] ![![-176495017, -10456274, -6633538]]
  ![![199, 0, 0]] where
 M := ![![![199, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC199 : ContainsPrimesAboveP 199 ![I199N0, I199N1, I199N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
    exact isPrimeI199N1
    exact isPrimeI199N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 199 (by decide) (𝕀 ⊙ MulI199N0 ⊙ MulI199N1)
instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![4, 44, 1]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0], ![4, 44, 1]] 
 ![![211, 0, 0], ![0, 211, 0], ![4, 44, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![4, 44, 1], ![110, -56, 133], ![6884, -658, 33]]]
  hmulB := by decide  
  f := ![![![-3, -44, -1], ![211, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-4, -44, 211]], ![![0, 0, 1], ![-2, -28, 133], ![32, -10, 33]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [25, 64, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [147, 210], [0, 1]]
 g := ![![[11, 76], [40, 79], [14], [55], [192, 47], [46], [147, 1]], ![[0, 135], [48, 132], [14], [55], [138, 164], [46], [83, 210]]]
 h' := ![![[147, 210], [55, 169], [22, 135], [168, 15], [53, 107], [53, 70], [123, 62], [0, 1]], ![[0, 1], [0, 42], [33, 76], [52, 196], [168, 104], [4, 141], [164, 149], [147, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49]]
 b := ![[], [151, 130]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [25, 64, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5591, 3909, -501]
  a := ![-3, -5, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-17, 123, -501]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![78, 1, 0]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![211, 0, 0], ![78, 1, 0]] 
 ![![211, 0, 0], ![78, 1, 0], ![178, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![78, 1, 0], ![-1, 77, 3], ![154, -16, 79]]]
  hmulB := by decide  
  f := ![![![-9153, 704858, 27462], ![0, -1931494, 0]], ![![-3383, 260491, 10149], ![1, -713813, 0]], ![![-7764, 594619, 23167], ![115, -1629412, 0]]]
  g := ![![![1, 0, 0], ![-78, 211, 0], ![-178, 0, 211]], ![![0, 1, 0], ![-31, 77, 3], ![-60, -16, 79]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![4, 44, 1]] ![![211, 0, 0], ![78, 1, 0]]
  ![![211, 0, 0]] where
 M := ![![![44521, 0, 0], ![16458, 211, 0]], ![![844, 9284, 211], ![422, 3376, 211]]]
 hmul := by decide  
 g := ![![![![211, 0, 0]], ![![78, 1, 0]]], ![![![4, 44, 1]], ![![2, 16, 1]]]]
 hle2 := by decide  


def PBC211 : ContainsPrimesAboveP 211 ![I211N0, I211N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
    exact isPrimeI211N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 211 (by decide) (𝕀 ⊙ MulI211N0)
instance hp223 : Fact (Nat.Prime 223) := {out := by norm_num}

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![101, 1, 0]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0], ![101, 1, 0]] 
 ![![223, 0, 0], ![101, 1, 0], ![201, 0, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![101, 1, 0], ![-1, 100, 3], ![154, -16, 102]]]
  hmulB := by decide  
  f := ![![![-4557, 455800, 13674], ![0, -1016434, 0]], ![![-2064, 206400, 6192], ![1, -460272, 0]], ![![-4126, 410833, 12325], ![41, -916158, 0]]]
  g := ![![![1, 0, 0], ![-101, 223, 0], ![-201, 0, 223]], ![![0, 1, 0], ![-48, 100, 3], ![-84, -16, 102]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N0 : Nat.card (O ⧸ I223N0) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N0)

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := prime_ideal_of_norm_prime hp223.out _ NI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15594317, -923870, -586110]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![-15594317, -923870, -586110]] 
 ![![223, 0, 0], ![149, 1, 0], ![8, 0, 1]] where
  M :=![![![-15594317, -923870, -586110], ![-89337070, -5292687, -3357720], ![-205575860, -12179140, -7726537]]]
  hmulB := by decide  
  f := ![![![25881, -7210, 1170]], ![![18133, -4753, 690]], ![![-3484, 500, 47]]]
  g := ![![![568391, -923870, -586110], ![3256211, -5292687, -3357720], ![7492952, -12179140, -7726537]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1

def I223N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![-27, 1, 0]] i)))

def SI223N2: IdealEqSpanCertificate' Table ![![223, 0, 0], ![-27, 1, 0]] 
 ![![223, 0, 0], ![196, 1, 0], ![45, 0, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![-27, 1, 0], ![-1, -28, 3], ![154, -16, -26]]]
  hmulB := by decide  
  f := ![![![-4421, -123816, 13266], ![0, -986106, 0]], ![![-3885, -108808, 11658], ![1, -866578, 0]], ![![-873, -24986, 2677], ![158, -198990, 0]]]
  g := ![![![1, 0, 0], ![-196, 223, 0], ![-45, 0, 223]], ![![-1, 1, 0], ![24, -28, 3], ![20, -16, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N2 : Nat.card (O ⧸ I223N2) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N2)

lemma isPrimeI223N2 : Ideal.IsPrime I223N2 := prime_ideal_of_norm_prime hp223.out _ NI223N2
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![223, 0, 0], ![101, 1, 0]] ![![-15594317, -923870, -586110]]
  ![![223, 0, 0], ![110, 83, 1]] where
 M := ![![![-3477532691, -206023010, -130702530]], ![![-1664363087, -98603557, -62554830]]]
 hmul := by decide  
 g := ![![![![-12724857, 1241268, -560024], ![-5817178, 0, 0]]], ![![![-6090169, 594081, -268030], ![-2784140, 0, 0]]]]
 hle2 := by decide  

def MulI223N1 : IdealMulLeCertificate' Table 
  ![![223, 0, 0], ![110, 83, 1]] ![![223, 0, 0], ![-27, 1, 0]]
  ![![223, 0, 0]] where
 M := ![![![49729, 0, 0], ![-6021, 223, 0]], ![![24530, 18509, 223], ![-2899, -2230, 223]]]
 hmul := by decide  
 g := ![![![![223, 0, 0]], ![![-27, 1, 0]]], ![![![110, 83, 1]], ![![-13, -10, 1]]]]
 hle2 := by decide  


def PBC223 : ContainsPrimesAboveP 223 ![I223N0, I223N1, I223N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
    exact isPrimeI223N1
    exact isPrimeI223N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 223 (by decide) (𝕀 ⊙ MulI223N0 ⊙ MulI223N1)
instance hp227 : Fact (Nat.Prime 227) := {out := by norm_num}

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![15, -71, 1]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0], ![15, -71, 1]] 
 ![![227, 0, 0], ![0, 227, 0], ![15, 156, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![15, -71, 1], ![225, 70, -212], ![-10826, 1182, -71]]]
  hmulB := by decide  
  f := ![![![-14, 71, -1], ![227, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-15, -156, 227]], ![![0, -1, 1], ![15, 146, -212], ![-43, 54, -71]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 2 2 7 [177, 211, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [16, 226], [0, 1]]
 g := ![![[191, 59], [54, 25], [188], [103], [26], [164, 112], [16, 1]], ![[0, 168], [0, 202], [188], [103], [26], [140, 115], [32, 226]]]
 h' := ![![[16, 226], [203, 115], [80, 222], [21, 85], [41, 28], [28, 139], [119, 79], [0, 1]], ![[0, 1], [0, 112], [0, 5], [19, 142], [35, 199], [209, 88], [21, 148], [16, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [225]]
 b := ![[], [8, 226]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 2
  hpos := by decide
  P := [177, 211, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![443925, 211204, -81862]
  a := ![1, 2, -67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7365, 57188, -81862]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![-15, 1, 0]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![227, 0, 0], ![-15, 1, 0]] 
 ![![227, 0, 0], ![212, 1, 0], ![71, 0, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![-15, 1, 0], ![-1, -16, 3], ![154, -16, -14]]]
  hmulB := by decide  
  f := ![![![-9679, -154880, 29040], ![0, -2197360, 0]], ![![-9039, -144640, 27120], ![1, -2052080, 0]], ![![-3022, -48443, 9083], ![81, -687280, 0]]]
  g := ![![![1, 0, 0], ![-212, 227, 0], ![-71, 0, 227]], ![![-1, 1, 0], ![14, -16, 3], ![20, -16, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![227, 0, 0], ![15, -71, 1]] ![![227, 0, 0], ![-15, 1, 0]]
  ![![227, 0, 0]] where
 M := ![![![51529, 0, 0], ![-3405, 227, 0]], ![![3405, -16117, 227], ![0, 1135, -227]]]
 hmul := by decide  
 g := ![![![![227, 0, 0]], ![![-15, 1, 0]]], ![![![15, -71, 1]], ![![0, 5, -1]]]]
 hle2 := by decide  


def PBC227 : ContainsPrimesAboveP 227 ![I227N0, I227N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI227N0
    exact isPrimeI227N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 227 (by decide) (𝕀 ⊙ MulI227N0)
instance hp229 : Fact (Nat.Prime 229) := {out := by norm_num}

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![-100, 16, 1]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0], ![-100, 16, 1]] 
 ![![229, 0, 0], ![0, 229, 0], ![129, 16, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![-100, 16, 1], ![138, -132, 49], ![2572, -210, -99]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-129, -16, 229]], ![![-1, 0, 1], ![-27, -4, 49], ![67, 6, -99]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 2 2 7 [143, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [182, 228], [0, 1]]
 g := ![![[82, 46], [99], [86, 70], [149], [181], [83, 25], [182, 1]], ![[210, 183], [99], [2, 159], [149], [181], [53, 204], [135, 228]]]
 h' := ![![[182, 228], [85, 59], [68, 102], [177, 38], [141, 81], [39, 69], [80, 5], [0, 1]], ![[0, 1], [60, 170], [83, 127], [223, 191], [227, 148], [2, 160], [74, 224], [182, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [175]]
 b := ![[], [167, 202]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 2
  hpos := by decide
  P := [143, 47, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2667, 4164, -1400]
  a := ![3, 4, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![777, 116, -1400]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![-49, 1, 0]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![229, 0, 0], ![-49, 1, 0]] 
 ![![229, 0, 0], ![180, 1, 0], ![99, 0, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![-49, 1, 0], ![-1, -50, 3], ![154, -16, -48]]]
  hmulB := by decide  
  f := ![![![1030, 48999, -2940], ![229, 224420, 0]], ![![820, 38499, -2310], ![230, 176330, 0]], ![![444, 21183, -1271], ![93, 97020, 0]]]
  g := ![![![1, 0, 0], ![-180, 229, 0], ![-99, 0, 229]], ![![-1, 1, 0], ![38, -50, 3], ![34, -16, -48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![229, 0, 0], ![-100, 16, 1]] ![![229, 0, 0], ![-49, 1, 0]]
  ![![229, 0, 0]] where
 M := ![![![52441, 0, 0], ![-11221, 229, 0]], ![![-22900, 3664, 229], ![5038, -916, 0]]]
 hmul := by decide  
 g := ![![![![229, 0, 0]], ![![-49, 1, 0]]], ![![![-100, 16, 1]], ![![22, -4, 0]]]]
 hle2 := by decide  


def PBC229 : ContainsPrimesAboveP 229 ![I229N0, I229N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI229N0
    exact isPrimeI229N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 229 (by decide) (𝕀 ⊙ MulI229N0)
instance hp233 : Fact (Nat.Prime 233) := {out := by norm_num}

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![233, 0, 0]] 
 ![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 3 2 7 [95, 31, 137, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [162, 110, 80], [167, 122, 153], [0, 1]]
 g := ![![[143, 132, 175], [209, 184], [133, 217], [189, 48, 38], [152, 167], [180, 141, 129], [1]], ![[216, 179, 192, 99], [16, 116], [3, 219], [11, 133, 84, 43], [213, 46], [115, 12, 67, 206], [183, 180, 39, 99]], ![[75, 148, 159, 5], [204, 196], [25, 38], [229, 93, 108, 86], [62, 102], [227, 125, 139, 6], [153, 137, 100, 134]]]
 h' := ![![[162, 110, 80], [128, 125, 116], [143, 6, 157], [219, 15, 110], [132, 184, 51], [142, 69, 20], [138, 202, 96], [0, 1]], ![[167, 122, 153], [80, 40, 153], [40, 226, 62], [201, 34, 174], [74, 156, 205], [51, 52, 38], [67, 204, 145], [162, 110, 80]], ![[0, 1], [143, 68, 197], [157, 1, 14], [193, 184, 182], [68, 126, 210], [42, 112, 175], [170, 60, 225], [167, 122, 153]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [209, 168], []]
 b := ![[], [214, 67, 161], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 3
  hpos := by decide
  P := [95, 31, 137, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11184, 96462, -30057]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-48, 414, -129]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 12649337 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def PBC233 : ContainsPrimesAboveP 233 ![I233N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI233N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![233, 0, 0]]) timesTableT_eq_Table B_one_repr 233 (by decide) 𝕀



lemma PB236I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 235 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 235 (by omega)

def PB236I4 : PrimesBelowBoundCertificateInterval O 193 235 236 where
  m := 7
  g := ![1, 3, 2, 3, 2, 2, 1]
  P := ![197, 199, 211, 223, 227, 229, 233]
  hP := PB236I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0]
    · exact ![I199N0, I199N1, I199N2]
    · exact ![I211N0, I211N1]
    · exact ![I223N0, I223N1, I223N2]
    · exact ![I227N0, I227N1]
    · exact ![I229N0, I229N1]
    · exact ![I233N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC197
    · exact PBC199
    · exact PBC211
    · exact PBC223
    · exact PBC227
    · exact PBC229
    · exact PBC233
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![7645373]
    · exact ![199, 199, 199]
    · exact ![44521, 211]
    · exact ![223, 223, 223]
    · exact ![51529, 227]
    · exact ![52441, 229]
    · exact ![12649337]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
      exact NI199N1
      exact NI199N2
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
      exact NI211N1
    · dsimp ; intro j
      fin_cases j
      exact NI223N0
      exact NI223N1
      exact NI223N2
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
      exact NI227N1
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
      exact NI229N1
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
  β := ![I199N0, I199N1, I199N2, I211N1, I223N0, I223N1, I223N2, I227N1, I229N1]
  Il := ![[], [I199N0, I199N1, I199N2], [I211N1], [I223N0, I223N1, I223N2], [I227N1], [I229N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
