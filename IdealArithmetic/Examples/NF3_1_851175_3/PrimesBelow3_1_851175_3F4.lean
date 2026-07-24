
import IdealArithmetic.Examples.NF3_1_851175_3.RI3_1_851175_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-245, 90, -9]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![-245, 90, -9]] 
 ![![197, 0, 0], ![5, 1, 0], ![121, 0, 1]] where
  M :=![![![-245, 90, -9], ![-1098, 160, 279], ![10647, -3591, -29]]]
  hmulB := by decide  
  f := ![![![-997249, -34929, -26550]], ![![-40228, -1409, -1071]], ![![-623891, -21852, -16610]]]
  g := ![![![2, 90, -9], ![-181, 160, 279], ![163, -3591, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N0 : Nat.card (O ⧸ I197N0) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N0)

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := prime_ideal_of_norm_prime hp197.out _ NI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1427, 50, 38]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![1427, 50, 38]] 
 ![![197, 0, 0], ![56, 1, 0], ![52, 0, 1]] where
  M :=![![![1427, 50, 38], ![4206, 147, 112], ![3206, 112, 85]]]
  hmulB := by decide  
  f := ![![![-49, 6, 14]], ![![-6, -1, 4]], ![![-14, 4, 1]]]
  g := ![![![-17, 50, 38], ![-50, 147, 112], ![-38, 112, 85]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1

def I197N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![601, 21, 16]] i)))

def SI197N2: IdealEqSpanCertificate' Table ![![601, 21, 16]] 
 ![![197, 0, 0], ![136, 1, 0], ![93, 0, 1]] where
  M :=![![![601, 21, 16], ![1771, 62, 47], ![1344, 49, 36]]]
  hmulB := by decide  
  f := ![![![-71, 28, -5]], ![![-52, 20, -3]], ![![-16, 7, -2]]]
  g := ![![![-19, 21, 16], ![-56, 62, 47], ![-44, 49, 36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N2 : Nat.card (O ⧸ I197N2) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N2)

lemma isPrimeI197N2 : Ideal.IsPrime I197N2 := prime_ideal_of_norm_prime hp197.out _ NI197N2
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![-245, 90, -9]] ![![1427, 50, 38]]
  ![![71, -28, 5]] where
 M := ![![![71, -28, 5]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI197N1 : IdealMulLeCertificate' Table 
  ![![71, -28, 5]] ![![601, 21, 16]]
  ![![197, 0, 0]] where
 M := ![![![-197, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC197 : ContainsPrimesAboveP 197 ![I197N0, I197N1, I197N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
    exact isPrimeI197N1
    exact isPrimeI197N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 197 (by decide) (𝕀 ⊙ MulI197N0 ⊙ MulI197N1)
instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![52, 34, 1]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0], ![52, 34, 1]] 
 ![![199, 0, 0], ![0, 199, 0], ![52, 34, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![52, 34, 1], ![78, 51, 101], ![3745, -1141, -16]]]
  hmulB := by decide  
  f := ![![![-51, -34, -1], ![199, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-52, -34, 199]], ![![0, 0, 1], ![-26, -17, 101], ![23, -3, -16]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [193, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [164, 198], [0, 1]]
 g := ![![[160, 33], [170, 72], [53, 49], [162], [79], [175], [164, 1]], ![[0, 166], [38, 127], [129, 150], [162], [79], [175], [129, 198]]]
 h' := ![![[164, 198], [25, 86], [119, 120], [41, 7], [8, 19], [176, 26], [188, 37], [0, 1]], ![[0, 1], [0, 113], [98, 79], [194, 192], [139, 180], [62, 173], [87, 162], [164, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94]]
 b := ![[], [126, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [193, 35, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1002, -49, -417]
  a := ![1, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![114, 71, -417]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![98, 1, 0]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![199, 0, 0], ![98, 1, 0]] 
 ![![199, 0, 0], ![98, 1, 0], ![16, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![98, 1, 0], ![-1, 99, 3], ![112, -35, 97]]]
  hmulB := by decide  
  f := ![![![18877, -1868724, -56628], ![0, 3756324, 0]], ![![9295, -920205, -27885], ![1, 1849705, 0]], ![![1436, -150250, -4553], ![166, 302016, 0]]]
  g := ![![![1, 0, 0], ![-98, 199, 0], ![-16, 0, 199]], ![![0, 1, 0], ![-49, 99, 3], ![10, -35, 97]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![52, 34, 1]] ![![199, 0, 0], ![98, 1, 0]]
  ![![199, 0, 0]] where
 M := ![![![39601, 0, 0], ![19502, 199, 0]], ![![10348, 6766, 199], ![5174, 3383, 199]]]
 hmul := by decide  
 g := ![![![![199, 0, 0]], ![![98, 1, 0]]], ![![![52, 34, 1]], ![![26, 17, 1]]]]
 hle2 := by decide  


def PBC199 : ContainsPrimesAboveP 199 ![I199N0, I199N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
    exact isPrimeI199N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 199 (by decide) (𝕀 ⊙ MulI199N0)
instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-15, -7, 1]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-15, -7, 1]] 
 ![![211, 0, 0], ![0, 211, 0], ![196, 204, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-15, -7, 1], ![119, -57, -22], ![-847, 294, -42]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-196, -204, 211]], ![![-1, -1, 1], ![21, 21, -22], ![35, 42, -42]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [15, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [200, 210], [0, 1]]
 g := ![![[57, 76], [184, 208], [73], [24], [53, 16], [53], [200, 1]], ![[65, 135], [6, 3], [73], [24], [88, 195], [53], [189, 210]]]
 h' := ![![[200, 210], [194, 42], [79, 29], [142, 101], [49, 92], [55, 4], [165, 106], [0, 1]], ![[0, 1], [154, 169], [182, 182], [86, 110], [92, 119], [11, 207], [54, 105], [200, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [121]]
 b := ![[], [69, 166]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [15, 11, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4041, 3136, -2136]
  a := ![-3, 0, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1965, 2080, -2136]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![22, 1, 0]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![211, 0, 0], ![22, 1, 0]] 
 ![![211, 0, 0], ![22, 1, 0], ![42, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![22, 1, 0], ![-1, 23, 3], ![112, -35, 21]]]
  hmulB := by decide  
  f := ![![![-5157, 118127, 15408], ![211, -1083696, 0]], ![![-557, 12304, 1605], ![212, -112885, 0]], ![![-1036, 23513, 3067], ![133, -215712, 0]]]
  g := ![![![1, 0, 0], ![-22, 211, 0], ![-42, 0, 211]], ![![0, 1, 0], ![-3, 23, 3], ![0, -35, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![-15, -7, 1]] ![![211, 0, 0], ![22, 1, 0]]
  ![![211, 0, 0]] where
 M := ![![![44521, 0, 0], ![4642, 211, 0]], ![![-3165, -1477, 211], ![-211, -211, 0]]]
 hmul := by decide  
 g := ![![![![211, 0, 0]], ![![22, 1, 0]]], ![![![-15, -7, 1]], ![![-1, -1, 0]]]]
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

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0]] 
 ![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 3 2 7 [187, 174, 57, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [40, 196, 34], [126, 26, 189], [0, 1]]
 g := ![![[125, 10, 139], [169, 7, 15], [19, 86, 8], [121, 151, 64], [201, 26, 30], [109, 127], [1]], ![[156, 165, 57, 144], [206, 167, 93, 82], [128, 103, 90, 171], [171, 216, 143, 136], [157, 185, 178, 220], [9, 183], [50, 127, 177, 56]], ![[221, 8, 56, 134], [115, 17, 161, 209], [175, 221, 53, 209], [192, 143, 168, 168], [202, 2, 88, 93], [36, 73], [142, 150, 146, 167]]]
 h' := ![![[40, 196, 34], [63, 61, 129], [15, 125, 98], [119, 180, 30], [100, 111, 215], [91, 61, 91], [36, 49, 166], [0, 1]], ![[126, 26, 189], [132, 8, 76], [33, 95, 108], [5, 16, 210], [68, 133, 221], [103, 46, 203], [15, 72, 184], [40, 196, 34]], ![[0, 1], [120, 154, 18], [204, 3, 17], [68, 27, 206], [33, 202, 10], [129, 116, 152], [49, 102, 96], [126, 26, 189]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [126, 177], []]
 b := ![[], [119, 29, 185], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 3
  hpos := by decide
  P := [187, 174, 57, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1045472837, -65969421, -393329853]
  a := ![1, -64, -67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4688219, -295827, -1763811]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 11089567 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def PBC223 : ContainsPrimesAboveP 223 ![I223N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![223, 0, 0]]) timesTableT_eq_Table B_one_repr 223 (by decide) 𝕀

instance hp227 : Fact (Nat.Prime 227) := {out := by norm_num}

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0]] 
 ![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 3 2 7 [54, 223, 120, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [172, 118, 137], [162, 108, 90], [0, 1]]
 g := ![![[207, 132, 57], [97, 66, 121], [136, 173], [72, 189], [36, 70], [130, 99, 99], [1]], ![[201, 176, 122, 94], [103, 162, 103, 106], [152, 155], [160, 71], [140, 205], [127, 43, 211, 41], [106, 192, 38, 124]], ![[62, 86, 17, 222], [68, 73, 101, 44], [51, 69], [16, 84], [89, 34], [9, 157, 188, 185], [148, 11, 178, 103]]]
 h' := ![![[172, 118, 137], [210, 65, 113], [116, 18, 216], [14, 23, 20], [161, 205, 102], [17, 133, 129], [173, 4, 107], [0, 1]], ![[162, 108, 90], [76, 188, 225], [145, 52, 143], [33, 84, 90], [156, 108, 57], [212, 206, 146], [194, 135, 73], [172, 118, 137]], ![[0, 1], [95, 201, 116], [155, 157, 95], [56, 120, 117], [100, 141, 68], [162, 115, 179], [225, 88, 47], [162, 108, 90]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69, 171], []]
 b := ![[], [109, 176, 70], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 3
  hpos := by decide
  P := [54, 223, 120, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3451762, 1834160, -856925]
  a := ![3, -1, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-15206, 8080, -3775]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 11697083 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def PBC227 : ContainsPrimesAboveP 227 ![I227N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI227N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![227, 0, 0]]) timesTableT_eq_Table B_one_repr 227 (by decide) 𝕀

instance hp229 : Fact (Nat.Prime 229) := {out := by norm_num}

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-105, -2, -3]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![-105, -2, -3]] 
 ![![229, 0, 0], ![0, 229, 0], ![35, 77, 1]] where
  M :=![![![-105, -2, -3], ![-334, -2, -3], ![-35, -77, -1]]]
  hmulB := by decide  
  f := ![![![1, -1, 0]], ![![1, 0, -3]], ![![0, 0, -1]]]
  g := ![![![0, 1, -3], ![-1, 1, -3], ![0, 0, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 2 2 7 [55, 224, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 228], [0, 1]]
 g := ![![[104, 25], [196], [217, 178], [165], [220], [161, 213], [5, 1]], ![[0, 204], [196], [191, 51], [165], [220], [81, 16], [10, 228]]]
 h' := ![![[5, 228], [25, 224], [202, 14], [43, 112], [88, 169], [76, 137], [183, 199], [0, 1]], ![[0, 1], [0, 5], [43, 215], [145, 117], [17, 60], [74, 92], [33, 30], [5, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [175]]
 b := ![[], [182, 202]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 2
  hpos := by decide
  P := [55, 224, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![17199, 7, 1499]
  a := ![-1, 21, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-154, -504, 1499]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 1, 0]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![-1, 1, 0]] 
 ![![229, 0, 0], ![228, 1, 0], ![76, 0, 1]] where
  M :=![![![-1, 1, 0], ![-1, 0, 3], ![112, -35, -2]]]
  hmulB := by decide  
  f := ![![![105, 2, 3]], ![![106, 2, 3]], ![![35, 1, 1]]]
  g := ![![![-1, 1, 0], ![-1, 0, 3], ![36, -35, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![-105, -2, -3]] ![![-1, 1, 0]]
  ![![229, 0, 0]] where
 M := ![![![-229, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P233P0 : CertificateIrreducibleZModOfList' 233 3 2 7 [93, 45, 187, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 56, 17], [21, 176, 216], [0, 1]]
 g := ![![[125, 93, 123], [192, 196], [94, 55], [213, 205, 131], [225, 76], [119, 229, 19], [1]], ![[25, 175, 134, 145], [154, 101], [2, 187], [55, 80, 217, 106], [58, 16], [175, 22, 102, 5], [228, 137, 76, 20]], ![[13, 143, 136, 228], [132, 132], [205, 92], [184, 126, 51, 147], [168, 129], [101, 173, 73, 151], [114, 158, 222, 213]]]
 h' := ![![[25, 56, 17], [159, 152, 194], [128, 182, 219], [229, 178, 145], [220, 220, 197], [117, 171, 141], [140, 188, 46], [0, 1]], ![[21, 176, 216], [94, 185, 147], [160, 171, 164], [146, 3, 120], [127, 99, 200], [66, 143, 229], [13, 216, 108], [25, 56, 17]], ![[0, 1], [199, 129, 125], [142, 113, 83], [69, 52, 201], [174, 147, 69], [120, 152, 96], [57, 62, 79], [21, 176, 216]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90, 128], []]
 b := ![[], [66, 130, 61], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 3
  hpos := by decide
  P := [93, 45, 187, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1033821, 474155, -159838]
  a := ![1, 1, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4437, 2035, -686]
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

instance hp239 : Fact (Nat.Prime 239) := {out := by norm_num}

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![75, 4, 1]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![239, 0, 0], ![75, 4, 1]] 
 ![![239, 0, 0], ![0, 239, 0], ![75, 4, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![75, 4, 1], ![108, 44, 11], ![385, -91, 37]]]
  hmulB := by decide  
  f := ![![![-74, -4, -1], ![239, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-75, -4, 239]], ![![0, 0, 1], ![-3, 0, 11], ![-10, -1, 37]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 2 2 7 [232, 195, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [44, 238], [0, 1]]
 g := ![![[177, 34], [218, 220], [201, 108], [231, 161], [101], [196, 5], [44, 1]], ![[0, 205], [99, 19], [173, 131], [145, 78], [101], [177, 234], [88, 238]]]
 h' := ![![[44, 238], [92, 150], [212, 69], [183, 158], [10, 219], [177, 36], [69, 31], [0, 1]], ![[0, 1], [0, 89], [141, 170], [204, 81], [86, 20], [88, 203], [238, 208], [44, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [147]]
 b := ![[], [56, 193]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 2
  hpos := by decide
  P := [232, 195, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1601, 1086, -87]
  a := ![-2, 3, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![34, 6, -87]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 57121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![-11, 1, 0]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![239, 0, 0], ![-11, 1, 0]] 
 ![![239, 0, 0], ![228, 1, 0], ![202, 0, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![-11, 1, 0], ![-1, -10, 3], ![112, -35, -12]]]
  hmulB := by decide  
  f := ![![![-25828, -258401, 77520], ![239, -6175760, 0]], ![![-24638, -246501, 73950], ![240, -5891350, 0]], ![![-21824, -218398, 65519], ![322, -5219680, 0]]]
  g := ![![![1, 0, 0], ![-228, 239, 0], ![-202, 0, 239]], ![![-1, 1, 0], ![7, -10, 3], ![44, -35, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N1)

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := prime_ideal_of_norm_prime hp239.out _ NI239N1
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![239, 0, 0], ![75, 4, 1]] ![![239, 0, 0], ![-11, 1, 0]]
  ![![239, 0, 0]] where
 M := ![![![57121, 0, 0], ![-2629, 239, 0]], ![![17925, 956, 239], ![-717, 0, 0]]]
 hmul := by decide  
 g := ![![![![239, 0, 0]], ![![-11, 1, 0]]], ![![![75, 4, 1]], ![![-3, 0, 0]]]]
 hle2 := by decide  


def PBC239 : ContainsPrimesAboveP 239 ![I239N0, I239N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI239N0
    exact isPrimeI239N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 239 (by decide) (𝕀 ⊙ MulI239N0)
instance hp241 : Fact (Nat.Prime 241) := {out := by norm_num}

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0], ![56, 78, 1]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![241, 0, 0], ![56, 78, 1]] 
 ![![241, 0, 0], ![0, 241, 0], ![56, 78, 1]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]], ![![56, 78, 1], ![34, 99, 233], ![8673, -2681, -56]]]
  hmulB := by decide  
  f := ![![![-55, -78, -1], ![241, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-56, -78, 241]], ![![0, 0, 1], ![-54, -75, 233], ![49, 7, -56]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 2 2 7 [180, 216, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 240], [0, 1]]
 g := ![![[194, 79], [118], [12], [154], [10, 182], [182, 164], [25, 1]], ![[0, 162], [118], [12], [154], [222, 59], [185, 77], [50, 240]]]
 h' := ![![[25, 240], [115, 140], [90, 212], [232, 112], [128, 40], [16, 69], [79, 204], [0, 1]], ![[0, 1], [0, 101], [88, 29], [140, 129], [164, 201], [54, 172], [118, 37], [25, 240]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66]]
 b := ![[], [190, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 2
  hpos := by decide
  P := [180, 216, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4180, -1580, -1905]
  a := ![0, -5, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![460, 610, -1905]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N0 B_one_repr
lemma NI241N0 : Nat.card (O ⧸ I241N0) = 58081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N0

def I241N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0], ![8, 1, 0]] i)))

def SI241N1: IdealEqSpanCertificate' Table ![![241, 0, 0], ![8, 1, 0]] 
 ![![241, 0, 0], ![8, 1, 0], ![56, 0, 1]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]], ![![8, 1, 0], ![-1, 9, 3], ![112, -35, 7]]]
  hmulB := by decide  
  f := ![![![-46005, 413981, 137994], ![241, -11085518, 0]], ![![-1534, 13733, 4578], ![242, -367766, 0]], ![![-10696, 96194, 32065], ![238, -2575888, 0]]]
  g := ![![![1, 0, 0], ![-8, 241, 0], ![-56, 0, 241]], ![![0, 1, 0], ![-1, 9, 3], ![0, -35, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N1 : Nat.card (O ⧸ I241N1) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N1)

lemma isPrimeI241N1 : Ideal.IsPrime I241N1 := prime_ideal_of_norm_prime hp241.out _ NI241N1
def MulI241N0 : IdealMulLeCertificate' Table 
  ![![241, 0, 0], ![56, 78, 1]] ![![241, 0, 0], ![8, 1, 0]]
  ![![241, 0, 0]] where
 M := ![![![58081, 0, 0], ![1928, 241, 0]], ![![13496, 18798, 241], ![482, 723, 241]]]
 hmul := by decide  
 g := ![![![![241, 0, 0]], ![![8, 1, 0]]], ![![![56, 78, 1]], ![![2, 3, 1]]]]
 hle2 := by decide  


def PBC241 : ContainsPrimesAboveP 241 ![I241N0, I241N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI241N0
    exact isPrimeI241N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 241 (by decide) (𝕀 ⊙ MulI241N0)
instance hp251 : Fact (Nat.Prime 251) := {out := by norm_num}

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, -3, -1]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![11, -3, -1]] 
 ![![251, 0, 0], ![57, 1, 0], ![69, 0, 1]] where
  M :=![![![11, -3, -1], ![-109, 43, -8], ![-273, 56, 48]]]
  hmulB := by decide  
  f := ![![![-2512, -88, -67]], ![![-600, -21, -16]], ![![-713, -25, -19]]]
  g := ![![![1, -3, -1], ![-8, 43, -8], ![-27, 56, 48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N0 : Nat.card (O ⧸ I251N0) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N0)

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := prime_ideal_of_norm_prime hp251.out _ NI251N0

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0], ![69, 1, 0]] i)))

def SI251N1: IdealEqSpanCertificate' Table ![![251, 0, 0], ![69, 1, 0]] 
 ![![251, 0, 0], ![69, 1, 0], ![63, 0, 1]] where
  M :=![![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]], ![![69, 1, 0], ![-1, 70, 3], ![112, -35, 68]]]
  hmulB := by decide  
  f := ![![![19413, -1358840, -58236], ![0, 4872412, 0]], ![![5336, -373520, -16008], ![1, 1339336, 0]], ![![4833, -341064, -14617], ![144, 1222956, 0]]]
  g := ![![![1, 0, 0], ![-69, 251, 0], ![-63, 0, 251]], ![![0, 1, 0], ![-20, 70, 3], ![-7, -35, 68]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N1 : Nat.card (O ⧸ I251N1) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N1)

lemma isPrimeI251N1 : Ideal.IsPrime I251N1 := prime_ideal_of_norm_prime hp251.out _ NI251N1

def I251N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0], ![125, 1, 0]] i)))

def SI251N2: IdealEqSpanCertificate' Table ![![251, 0, 0], ![125, 1, 0]] 
 ![![251, 0, 0], ![125, 1, 0], ![188, 0, 1]] where
  M :=![![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]], ![![125, 1, 0], ![-1, 126, 3], ![112, -35, 124]]]
  hmulB := by decide  
  f := ![![![41833, -5270832, -125496], ![0, 10499832, 0]], ![![20832, -2624832, -62496], ![1, 5228832, 0]], ![![31354, -3947874, -93997], ![-42, 7864416, 0]]]
  g := ![![![1, 0, 0], ![-125, 251, 0], ![-188, 0, 251]], ![![0, 1, 0], ![-65, 126, 3], ![-75, -35, 124]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N2 : Nat.card (O ⧸ I251N2) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N2)

lemma isPrimeI251N2 : Ideal.IsPrime I251N2 := prime_ideal_of_norm_prime hp251.out _ NI251N2
def MulI251N0 : IdealMulLeCertificate' Table 
  ![![11, -3, -1]] ![![251, 0, 0], ![69, 1, 0]]
  ![![251, 0, 0], ![-28, 126, 1]] where
 M := ![![![2761, -753, -251], ![650, -164, -77]]]
 hmul := by decide  
 g := ![![![![11, -3, -1], ![0, 0, 0]], ![![22, -88, -1], ![174, 0, 0]]]]
 hle2 := by decide  

def MulI251N1 : IdealMulLeCertificate' Table 
  ![![251, 0, 0], ![-28, 126, 1]] ![![251, 0, 0], ![125, 1, 0]]
  ![![251, 0, 0]] where
 M := ![![![63001, 0, 0], ![31375, 251, 0]], ![![-7028, 31626, 251], ![-3514, 15813, 502]]]
 hmul := by decide  
 g := ![![![![251, 0, 0]], ![![125, 1, 0]]], ![![![-28, 126, 1]], ![![-14, 63, 2]]]]
 hle2 := by decide  


def PBC251 : ContainsPrimesAboveP 251 ![I251N0, I251N1, I251N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI251N0
    exact isPrimeI251N1
    exact isPrimeI251N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 251 (by decide) (𝕀 ⊙ MulI251N0 ⊙ MulI251N1)
instance hp257 : Fact (Nat.Prime 257) := {out := by norm_num}

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![257, 0, 0]] 
 ![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]] where
  M :=![![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P0 : CertificateIrreducibleZModOfList' 257 3 2 8 [233, 57, 44, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [245, 119, 15], [225, 137, 242], [0, 1]]
 g := ![![[128, 17, 92], [220, 32], [50, 234], [10, 17], [8, 116], [160, 232], [213, 1], []], ![[216, 43, 229, 81], [134, 120], [198, 36], [186, 9], [107, 255], [52, 21], [185, 8], [95, 225]], ![[41, 137, 123, 46], [103, 187], [29, 98], [41, 120], [127, 124], [96, 120], [76, 26], [125, 225]]]
 h' := ![![[245, 119, 15], [117, 43, 116], [100, 194, 240], [106, 80, 100], [196, 57, 187], [255, 118, 87], [229, 219, 80], [0, 0, 1], [0, 1]], ![[225, 137, 242], [141, 13, 89], [254, 190, 67], [223, 237, 251], [223, 97, 3], [15, 191, 68], [56, 182, 110], [111, 213, 137], [245, 119, 15]], ![[0, 1], [98, 201, 52], [14, 130, 207], [54, 197, 163], [163, 103, 67], [131, 205, 102], [59, 113, 67], [169, 44, 119], [225, 137, 242]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [195, 167], []]
 b := ![[], [231, 101, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 3
  hpos := by decide
  P := [233, 57, 44, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7648063, -2717518, 160368]
  a := ![-2, -6, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![29759, -10574, 624]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N0 B_one_repr
lemma NI257N0 : Nat.card (O ⧸ I257N0) = 16974593 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N0

def PBC257 : ContainsPrimesAboveP 257 ![I257N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI257N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![257, 0, 0]]) timesTableT_eq_Table B_one_repr 257 (by decide) 𝕀



lemma PB262I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 261 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 261 (by omega)

def PB262I4 : PrimesBelowBoundCertificateInterval O 193 261 262 where
  m := 11
  g := ![3, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257]
  hP := PB262I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1, I197N2]
    · exact ![I199N0, I199N1]
    · exact ![I211N0, I211N1]
    · exact ![I223N0]
    · exact ![I227N0]
    · exact ![I229N0, I229N1]
    · exact ![I233N0]
    · exact ![I239N0, I239N1]
    · exact ![I241N0, I241N1]
    · exact ![I251N0, I251N1, I251N2]
    · exact ![I257N0]
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
    · exact PBC239
    · exact PBC241
    · exact PBC251
    · exact PBC257
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![197, 197, 197]
    · exact ![39601, 199]
    · exact ![44521, 211]
    · exact ![11089567]
    · exact ![11697083]
    · exact ![52441, 229]
    · exact ![12649337]
    · exact ![57121, 239]
    · exact ![58081, 241]
    · exact ![251, 251, 251]
    · exact ![16974593]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
      exact NI197N2
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
      exact NI199N1
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
      exact NI211N1
    · dsimp ; intro j
      fin_cases j
      exact NI223N0
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
      exact NI229N1
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
      exact NI239N1
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
      exact NI241N1
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
      exact NI251N1
      exact NI251N2
    · dsimp ; intro j
      fin_cases j
      exact NI257N0
  β := ![I197N0, I197N1, I197N2, I199N1, I211N1, I229N1, I239N1, I241N1, I251N0, I251N1, I251N2]
  Il := ![[I197N0, I197N1, I197N2], [I199N1], [I211N1], [], [], [I229N1], [], [I239N1], [I241N1], [I251N0, I251N1, I251N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
