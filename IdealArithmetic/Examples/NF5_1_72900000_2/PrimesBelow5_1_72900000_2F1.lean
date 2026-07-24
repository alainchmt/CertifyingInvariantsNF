
import IdealArithmetic.Examples.NF5_1_72900000_2.RI5_1_72900000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 1, 2, -5, 60]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-5, 1, 2, -5, 60]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![20, 13, 1, 0, 0], ![1, 25, 0, 1, 0], ![9, 21, 0, 0, 1]] where
  M :=![![![-5, 1, 2, -5, 60], ![20, 35, 26, -28, 70], ![112, -22, -91, 124, -1204], ![-496, -596, -358, 369, -32], ![-92, -45, 6, -19, 507]]]
  hmulB := by decide  
  f := ![![![1427, 4525, 4970, -743, 10962]], ![![2972, 9417, 10286, -1534, 22678]], ![![2528, 8015, 8775, -1310, 19350]], ![![3051, 9670, 10566, -1576, 23296]], ![![2627, 8325, 9102, -1358, 20069]]]
  g := ![![![-20, -40, 2, -5, 60], ![-38, -37, 26, -28, 70], ![436, 805, -91, 124, -1204], ![227, -155, -358, 369, -32], ![-164, -355, 6, -19, 507]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [3, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14, 28], [0, 1]]
 g := ![![[5, 22], [16], [7, 13], [14, 1]], ![[23, 7], [16], [15, 16], [28, 28]]]
 h' := ![![[14, 28], [16, 15], [8, 25], [16, 19], [0, 1]], ![[0, 1], [23, 14], [10, 4], [21, 10], [14, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [13, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [3, 15, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5077, 5923, 9768, -11995, 93148]
  a := ![10, -11, -18, 14, -145]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-35406, -61286, 9768, -11995, 93148]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 1, 2, -1, 14]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![-1, 1, 2, -1, 14]] 
 ![![29, 0, 0, 0, 0], ![23, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![-1, 1, 2, -1, 14], ![4, 9, 8, -6, 26], ![24, 6, -7, 18, -192], ![-72, -96, -60, 77, -108], ![-16, -9, 0, -1, 77]]]
  hmulB := by decide  
  f := ![![![1407, 781, -874, 253, -2344]], ![![1081, 622, -686, 199, -1838]], ![![1074, 572, -651, 188, -1748]], ![![792, 452, -500, 145, -1340]], ![![831, 464, -518, 150, -1389]]]
  g := ![![![-10, 1, 2, -1, 14], ![-25, 9, 8, -6, 26], ![104, 6, -7, 18, -192], ![140, -96, -60, 77, -108], ![-38, -9, 0, -1, 77]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 50, -35, 11, -90]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![7, 50, -35, 11, -90]] 
 ![![29, 0, 0, 0, 0], ![23, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![7, 50, -35, 11, -90], ![-44, -39, 37, -11, 98], ![44, 10, -18, 5, -50], ![-20, 14, -5, 2, -10], ![-4, 6, -3, 1, -7]]]
  hmulB := by decide  
  f := ![![![-13, -34, -35, 5, -66]], ![![-11, -29, -30, 4, -56]], ![![-10, -30, -32, 5, -70]], ![![-12, -34, -35, 10, -86]], ![![-5, -12, -12, 2, -21]]]
  g := ![![![9, 50, -35, 11, -90], ![-23, -39, 37, -11, 98], ![20, 10, -18, 5, -50], ![-6, 14, -5, 2, -10], ![-1, 6, -3, 1, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2

def I29N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1173, -3698, -4033, 601, -8890]] i)))

def SI29N3: IdealEqSpanCertificate' Table ![![-1173, -3698, -4033, 601, -8890]] 
 ![![29, 0, 0, 0, 0], ![28, 1, 0, 0, 0], ![28, 0, 1, 0, 0], ![28, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![-1173, -3698, -4033, 601, -8890], ![-2404, -7659, -8381, 1251, -18482], ![-5004, -15882, -17384, 2595, -38334], ![-10380, -32958, -36051, 5380, -79494], ![-756, -2398, -2621, 391, -5779]]]
  hmulB := by decide  
  f := ![![![-97, 58, 119, -157, 1334]], ![![-72, 77, 125, -161, 1250]], ![![-56, 2, 32, -47, 514]], ![![-512, -262, 19, -88, 2710]], ![![-74, 6, 51, -71, 733]]]
  g := ![![![8683, -3698, -4033, 601, -8890], ![18020, -7659, -8381, 1251, -18482], ![37372, -15882, -17384, 2595, -38334], ![77524, -32958, -36051, 5380, -79494], ![5638, -2398, -2621, 391, -5779]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N3 : Nat.card (O ⧸ I29N3) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N3)

lemma isPrimeI29N3 : Ideal.IsPrime I29N3 := prime_ideal_of_norm_prime hp29.out _ NI29N3
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-5, 1, 2, -5, 60]] ![![-1, 1, 2, -1, 14]]
  ![![-543, -44, 284, -410, 4732]] where
 M := ![![![-543, -44, 284, -410, 4732]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![-543, -44, 284, -410, 4732]] ![![7, 50, -35, 11, -90]]
  ![![-97, 58, 119, -157, 1334]] where
 M := ![![![-97, 58, 119, -157, 1334]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI29N2 : IdealMulLeCertificate' Table 
  ![![-97, 58, 119, -157, 1334]] ![![-1173, -3698, -4033, 601, -8890]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![29, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1, I29N2, I29N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
    exact isPrimeI29N2
    exact isPrimeI29N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0 ⊙ MulI29N1 ⊙ MulI29N2)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0, 0, 0]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]] where
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 5 2 4 [9, 13, 27, 10, 28, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 24, 13, 9, 1], [9, 17, 30, 14, 30], [13, 23, 7, 30, 5], [19, 28, 12, 9, 26], [0, 1]]
 g := ![![[18, 17, 22, 0, 19], [19, 25, 8, 17, 4], [30, 3, 1], []], ![[30, 3, 15, 1, 20, 10, 27, 18], [27, 4, 1, 0, 27, 15, 22, 9], [20, 9, 23, 18, 18, 0, 17, 9], [20, 1, 18, 30, 30, 21, 30, 1]], ![[6, 16, 0, 27, 5, 9, 16, 22], [0, 28, 26, 10, 4, 30, 27, 17], [12, 23, 5, 27, 8, 0, 6, 3], [21, 19, 4, 20, 8, 1, 8, 30]], ![[13, 26, 19, 21, 30, 16, 13, 7], [20, 23, 20, 17, 5, 20, 13, 1], [28, 10, 20, 6, 13, 7, 14, 18], [14, 12, 9, 10, 18, 4, 21, 1]], ![[20, 5, 27, 10, 13, 6, 6, 6], [12, 26, 15, 17, 20, 6, 26, 23], [7, 10, 2, 10, 19, 7, 3, 24], [25, 2, 4, 29, 13, 6, 21, 30]]]
 h' := ![![[24, 24, 13, 9, 1], [15, 12, 16, 29, 22], [9, 17, 10, 9, 2], [0, 0, 0, 1], [0, 1]], ![[9, 17, 30, 14, 30], [0, 22, 25, 29, 24], [18, 5, 10, 27, 3], [4, 4, 12, 10, 28], [24, 24, 13, 9, 1]], ![[13, 23, 7, 30, 5], [2, 23, 14, 19, 3], [18, 27, 10, 13, 18], [13, 29, 14, 25, 11], [9, 17, 30, 14, 30]], ![[19, 28, 12, 9, 26], [19, 30, 25, 3, 19], [30, 8, 3, 21, 26], [25, 25, 5, 18, 4], [13, 23, 7, 30, 5]], ![[0, 1], [4, 6, 13, 13, 25], [30, 5, 29, 23, 13], [0, 4, 0, 8, 19], [19, 28, 12, 9, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30, 8, 27, 17], [], [], []]
 b := ![[], [3, 5, 19, 22, 14], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 5
  hpos := by decide
  P := [9, 13, 27, 10, 28, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2442802442800, -450859850340, 996827234254, -1506157958228, 19303518871588]
  a := ![-9, -52, 17, -13, 132]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-78800078800, -14543866140, 32155717234, -48585740588, 622694157148]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 28629151 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def PBC31 : ContainsPrimesAboveP 31 ![I31N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![31, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 31 (by decide) 𝕀

instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![87573263, 278107789, 304281659, -45413818, 670967514]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![87573263, 278107789, 304281659, -45413818, 670967514]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![25, 19, 1, 0, 0], ![6, 34, 0, 1, 0], ![32, 33, 0, 0, 1]] where
  M :=![![![87573263, 278107789, 304281659, -45413818, 670967514], ![181655272, 576885505, 631178577, -94202947, 1391803640], ![376811788, 1196647124, 1309268516, -195407381, 2887050914], ![781629524, 2482233178, 2715846371, -405338112, 5988677386], ![56846880, 180529531, 197519909, -29479704, 435548573]]]
  hmulB := by decide  
  f := ![![![41663, -643, -10121, 2478, -29112]], ![![-9912, 22463, -12409, 4123, -30948]], ![![22615, 10442, -12660, 3624, -34118]], ![![-1682, 20866, -13431, 4302, -34210]], ![![27404, 19550, -19922, 5849, -53057]]]
  g := ![![![-776160696, -705435186, 304281659, -45413818, 670967514], ![-1610008323, -1463300740, 631178577, -94202947, 1391803640], ![-3339678002, -3035359024, 1309268516, -195407381, 2887050914], ![-6927572363, -6296316373, 2715846371, -405338112, 5988677386], ![-503833161, -457922749, 197519909, -29479704, 435548573]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [30, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 36], [0, 1]]
 g := ![![[5, 21], [27], [4, 1], [4], [1]], ![[0, 16], [27], [2, 36], [4], [1]]]
 h' := ![![[35, 36], [11, 24], [28, 8], [3, 1], [7, 35], [0, 1]], ![[0, 1], [0, 13], [12, 29], [1, 36], [11, 2], [35, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [30, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [30, 2, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-497, 532, 933, -1123, 8989]
  a := ![3, -5, -5, 4, -43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8236, -7450, 933, -1123, 8989]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8281, 7509, -7082, 2105, -18752]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![8281, 7509, -7082, 2105, -18752]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![10, 3, 1, 0, 0], ![7, 1, 0, 1, 0], ![35, 12, 0, 0, 1]] where
  M :=![![![8281, 7509, -7082, 2105, -18752], ![-8420, -2051, 3492, -960, 9578], ![3840, -2682, 807, -326, 1788], ![1304, 4324, -3176, 975, -8180], ![756, 1379, -1104, 337, -2887]]]
  hmulB := by decide  
  f := ![![![-10613471, -33705367, -36877518, 5503943, -81318134]], ![![-22015772, -69915833, -76495900, 11416958, -168680110]], ![![-5887834, -18698087, -20457841, 3053318, -45111318]], ![![-5163241, -16396986, -17940174, 2677558, -39559644]], ![![-17366225, -55150194, -60340606, 9005792, -133056283]]]
  g := ![![![19478, 6802, -7082, 2105, -18752], ![-10050, -3419, 3492, -960, 9578], ![-1744, -709, 807, -326, 1788], ![8447, 3001, -3176, 975, -8180], ![2986, 1054, -1104, 337, -2887]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P1 : CertificateIrreducibleZModOfList' 37 2 2 5 [15, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 36], [0, 1]]
 g := ![![[30, 11], [28], [30, 1], [36], [1]], ![[1, 26], [28], [24, 36], [36], [1]]]
 h' := ![![[31, 36], [23, 23], [31, 18], [18, 1], [22, 31], [0, 1]], ![[0, 1], [33, 14], [34, 19], [12, 36], [21, 6], [31, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [28, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N1 : CertifiedPrimeIdeal' SI37N1 37 where
  n := 2
  hpos := by decide
  P := [15, 6, 1]
  hirr := P37P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2242, 23480, 27995, -31864, 200660]
  a := ![-15, 35, 27, -23, 218]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-191412, -65853, 27995, -31864, 200660]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N1 B_one_repr
lemma NI37N1 : Nat.card (O ⧸ I37N1) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 4, -3, 1, -8]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![1, 4, -3, 1, -8]] 
 ![![37, 0, 0, 0, 0], ![15, 1, 0, 0, 0], ![34, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![28, 0, 0, 0, 1]] where
  M :=![![![1, 4, -3, 1, -8], ![-4, -3, 3, -1, 10], ![4, 2, 0, -1, 2], ![4, 2, -3, 4, -46], ![0, 0, -1, 1, -7]]]
  hmulB := by decide  
  f := ![![![5, 36, 53, -9, 120]], ![![3, 17, 24, -4, 54]], ![![6, 38, 54, -9, 122]], ![![4, 18, 23, -4, 54]], ![![4, 28, 41, -7, 93]]]
  g := ![![![7, 4, -3, 1, -8], ![-9, -3, 3, -1, 10], ![-2, 2, 0, -1, 2], ![36, 2, -3, 4, -46], ![6, 0, -1, 1, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![87573263, 278107789, 304281659, -45413818, 670967514]] ![![8281, 7509, -7082, 2105, -18752]]
  ![![-5, -36, -53, 9, -120]] where
 M := ![![![-5, -36, -53, 9, -120]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![-5, -36, -53, 9, -120]] ![![1, 4, -3, 1, -8]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![-37, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0, 0, 0]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]] where
  M :=![![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 5 2 5 [39, 28, 11, 36, 11, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 27, 7, 6, 13], [9, 33, 19, 33, 30], [14, 19, 37, 4, 5], [40, 2, 19, 39, 34], [0, 1]]
 g := ![![[4, 3, 24, 5, 25], [24, 6, 4, 4], [20, 36, 35, 39], [1], []], ![[25, 18, 25, 29, 5, 4, 3, 14], [0, 7, 32, 9], [36, 21, 31, 40], [9, 11, 30, 11, 32, 29, 3, 19], [1, 34, 19, 5]], ![[8, 14, 31, 14, 12, 32, 26, 11], [31, 5, 8, 4], [29, 11, 35, 10], [27, 23, 29, 40, 13, 36, 27, 35], [23, 0, 34, 39]], ![[5, 37, 20, 33, 22, 24, 30, 36], [1, 32, 10, 1], [33, 29, 24, 18], [17, 19, 36, 22, 11, 8, 40, 37], [35, 21, 11, 25]], ![[1, 15, 17, 36, 2, 35, 35, 19], [3, 5, 11, 4], [28, 5, 31, 5], [39, 8, 18, 22, 29, 28, 33, 24], [20, 28, 22, 8]]]
 h' := ![![[8, 27, 7, 6, 13], [16, 4, 40, 28, 5], [3, 15, 33, 12, 2], [2, 13, 30, 5, 30], [0, 0, 1], [0, 1]], ![[9, 33, 19, 33, 30], [0, 14, 9, 33, 15], [0, 31, 8, 15, 3], [16, 35, 10, 33, 9], [25, 21, 39, 34, 22], [8, 27, 7, 6, 13]], ![[14, 19, 37, 4, 5], [31, 16, 33, 14, 9], [25, 6, 24, 28, 39], [34, 31, 33, 7, 25], [4, 32, 16, 23, 7], [9, 33, 19, 33, 30]], ![[40, 2, 19, 39, 34], [34, 18, 32, 23, 9], [27, 27, 2, 10, 40], [17, 13, 21, 34, 31], [20, 4, 36, 15, 27], [14, 19, 37, 4, 5]], ![[0, 1], [24, 30, 9, 25, 3], [31, 3, 15, 17, 39], [37, 31, 29, 3, 28], [0, 25, 31, 10, 26], [40, 2, 19, 39, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 26, 7, 34], [], [], []]
 b := ![[], [31, 27, 13, 26, 10], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 5
  hpos := by decide
  P := [39, 28, 11, 36, 11, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-155938547796304, -97430379197576, -12353626970367, -4504752380316, 695388024597160]
  a := ![19, -20, -33, 30, -276]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3803379214544, -2376350712136, -301307974887, -109872009276, 16960683526760]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 115856201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def PBC41 : ContainsPrimesAboveP 41 ![I41N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![41, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 41 (by decide) 𝕀

instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0, 0, 0]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![0, 0, 0, 0, 43]] where
  M :=![![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![0, 0, 0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 5 2 5 [23, 0, 27, 10, 38, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 20, 28, 32, 29], [18, 26, 25, 0, 11], [9, 36, 26, 37, 19], [7, 3, 7, 17, 27], [0, 1]]
 g := ![![[5, 22, 39, 29, 25], [33, 0, 20, 41, 14], [32, 6, 25, 25], [1], []], ![[41, 40, 17, 21, 38, 28, 25, 42], [13, 14, 15, 21, 16, 23, 33, 42], [38, 38, 13, 31], [23, 37, 9, 10, 17, 17, 12, 37], [38, 33, 41, 24]], ![[20, 9, 32, 36, 26, 38], [2, 24, 16, 0, 19, 16, 27, 10], [41, 2, 27, 13], [18, 22, 6, 5, 16, 25], [27, 0, 3, 35]], ![[34, 15, 19, 5, 15, 23, 33, 8], [18, 28, 15, 13, 31, 30, 38, 27], [8, 19, 25, 23], [4, 26, 27, 12, 36, 13, 23, 30], [13, 10, 29, 17]], ![[30, 24, 6, 33, 20, 34, 35, 22], [5, 20, 17, 1, 34, 40, 41, 29], [36, 15, 29, 14], [20, 9, 36, 5, 26, 32, 20, 39], [8, 24, 5, 41]]]
 h' := ![![[14, 20, 28, 32, 29], [15, 21, 10, 42, 5], [8, 34, 18, 5, 10], [20, 0, 16, 33, 5], [0, 0, 1], [0, 1]], ![[18, 26, 25, 0, 11], [27, 36, 1, 2, 30], [21, 27, 33, 32, 13], [11, 39, 18, 32, 26], [10, 16, 32, 21, 38], [14, 20, 28, 32, 29]], ![[9, 36, 26, 37, 19], [9, 5, 23, 25], [12, 19, 17, 13, 13], [3, 18, 29, 27, 20], [4, 33, 4, 10], [18, 26, 25, 0, 11]], ![[7, 3, 7, 17, 27], [4, 4, 25, 32, 10], [23, 21, 0, 35, 31], [32, 30, 3, 24, 25], [40, 31, 15, 27, 26], [9, 36, 26, 37, 19]], ![[0, 1], [17, 20, 27, 28, 41], [38, 28, 18, 1, 19], [7, 42, 20, 13, 10], [37, 6, 34, 28, 22], [7, 3, 7, 17, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39, 20, 8, 7], [], [], []]
 b := ![[], [22, 11, 37, 33, 22], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 5
  hpos := by decide
  P := [23, 0, 27, 10, 38, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-56565221409921, -52196604937576, -23147063385896, 20872080575068, 120380256032108]
  a := ![-12, 12, 22, -28, 174]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1315470265347, -1213874533432, -538303799672, 485397222676, 2799540837956]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 147008443 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def PBC43 : ContainsPrimesAboveP 43 ![I43N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![43, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 43 (by decide) 𝕀

instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![35, 3, -16, 37, -334]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![35, 3, -16, 37, -334]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![40, 37, 22, 2, 1]] where
  M :=![![![35, 3, -16, 37, -334], ![-148, -151, -72, 96, 142], ![-384, 378, 663, -790, 6420], ![3160, 2876, 1268, -1017, -7300], ![456, 121, -144, 239, -3335]]]
  hmulB := by decide  
  f := ![![![-311, 173, -36, 17, -68]], ![![-68, -311, 224, -70, 578]], ![![280, 230, -223, 66, -592]], ![![-264, -48, 100, -27, 276]], ![![-200, 8, 46, -11, 133]]]
  g := ![![![285, 263, 156, 15, -334], ![-124, -115, -68, -4, 142], ![-5472, -5046, -2991, -290, 6420], ![6280, 5808, 3444, 289, -7300], ![2848, 2628, 1558, 147, -3335]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 4 2 5 [15, 23, 21, 3, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 43, 15, 35], [27, 24, 27, 41], [41, 26, 5, 18], [0, 1]]
 g := ![![[11, 18, 36, 17], [34, 38, 31, 2], [23, 46, 18, 3], [44, 1], []], ![[21, 35, 20, 18, 28, 31], [41, 5, 37, 0, 26, 29], [8, 44, 27, 42, 43, 20], [21, 14, 16, 11, 45, 35], [2, 7, 3]], ![[26, 24, 28, 27, 19, 35], [25, 7, 21, 42, 18, 19], [38, 45, 3, 21, 26, 13], [36, 11, 0, 0, 5, 10], [41, 38, 36]], ![[27, 45, 3, 1, 31, 36], [18, 35, 46, 1, 28, 6], [21, 10, 12, 11, 7, 25], [35, 30, 0, 27, 37, 42], [11, 7, 42]]]
 h' := ![![[23, 43, 15, 35], [7, 32, 26, 8], [31, 7, 41, 40], [45, 7, 40, 35], [0, 0, 1], [0, 1]], ![[27, 24, 27, 41], [31, 11, 37, 39], [20, 26, 39, 5], [40, 18, 33, 25], [29, 41, 35, 46], [23, 43, 15, 35]], ![[41, 26, 5, 18], [3, 3, 40, 40], [22, 5, 34, 6], [14, 35, 11, 32], [20, 18, 41, 22], [27, 24, 27, 41]], ![[0, 1], [12, 1, 38, 7], [0, 9, 27, 43], [21, 34, 10, 2], [12, 35, 17, 26], [41, 26, 5, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [29, 21, 20], []]
 b := ![[], [], [17, 24, 5, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 4
  hpos := by decide
  P := [15, 23, 21, 3, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-808778369, 1071048824, 1685135844, -2111075696, 15892428844]
  a := ![1, 11, 2, 9, -8]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-13542679407, -12488272732, -7403155292, -721190072, 15892428844]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 4879681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![311, -173, 36, -17, 68]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![311, -173, 36, -17, 68]] 
 ![![47, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![44, 0, 0, 1, 0], ![38, 0, 0, 0, 1]] where
  M :=![![![311, -173, 36, -17, 68], ![68, 311, -224, 70, -578], ![-280, -230, 223, -66, 592], ![264, 48, -100, 27, -276], ![76, 1, -20, 5, -57]]]
  hmulB := by decide  
  f := ![![![-35, -3, 16, -37, 334]], ![![-11, 2, 8, -17, 132]], ![![-3, -9, -9, 5, -30]], ![![-100, -64, -12, -13, 468]], ![![-38, -5, 16, -35, 341]]]
  g := ![![![26, -173, 36, -17, 68], ![349, 311, -224, 70, -578], ![-401, -230, 223, -66, 592], ![216, 48, -100, 27, -276], ![49, 1, -20, 5, -57]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![35, 3, -16, 37, -334]] ![![311, -173, 36, -17, 68]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![-47, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-789, 43, 526, -733, 7670]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-789, 43, 526, -733, 7670]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![25, 6, 22, 1, 0], ![4, 29, 17, 0, 1]] where
  M :=![![![-789, 43, 526, -733, 7670], ![2932, 3949, 2582, -2746, 3506], ![10984, -4546, -11767, 15552, -138232], ![-62208, -65040, -33914, 33153, 72624], ![-10304, -3983, 1902, -3575, 65149]]]
  hmulB := by decide  
  f := ![![![605995, 1924511, 2105646, -314267, 4643136]], ![![1257068, 3992063, 4367778, -651888, 9631330]], ![![2607552, 8280846, 9060177, -1352224, 19978476]], ![![1612591, 5121149, 5603122, -836262, 12355372]], ![![1577372, 5009274, 5480717, -817993, 12085457]]]
  g := ![![![-248, -4113, -2146, -733, 7670], ![1086, -1533, 64, -2746, 3506], ![3304, 73790, 37661, 15552, -138232], ![-22293, -44718, -37696, 33153, 72624], ![-3425, -35318, -19377, -3575, 65149]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [31, 43, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 47, 25], [35, 5, 28], [0, 1]]
 g := ![![[8, 28, 29], [25, 49], [1, 27, 43], [32, 1], [1]], ![[7, 3, 24, 28], [48, 49], [33, 33, 47, 29], [0, 29], [42, 29, 49, 43]], ![[24, 7, 49, 44], [], [46, 47, 30, 46], [36, 17], [10, 1, 37, 10]]]
 h' := ![![[17, 47, 25], [27, 16, 20], [22, 28, 7], [22, 40, 34], [22, 10, 52], [0, 1]], ![[35, 5, 28], [24, 17, 23], [44, 12, 46], [49, 21, 4], [7, 43, 33], [17, 47, 25]], ![[0, 1], [10, 20, 10], [13, 13], [33, 45, 15], [6, 0, 21], [35, 5, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 19], []]
 b := ![[], [15, 18, 48], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [31, 43, 1, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1086160, 1221606, 687559, -693782, -594882]
  a := ![-5, 1, 9, -9, 72]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![392646, 427092, 491769, -693782, -594882]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 25, -13, 2, -32]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![7, 25, -13, 2, -32]] 
 ![![53, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![32, 0, 0, 1, 0], ![15, 0, 0, 0, 1]] where
  M :=![![![7, 25, -13, 2, -32], ![-8, -17, 7, 7, -76], ![-28, -56, -44, 41, -50], ![-164, 86, 181, -240, 2078], ![4, 35, 31, -38, 199]]]
  hmulB := by decide  
  f := ![![![714327, 2268505, 2482007, -370438, 5473042]], ![![189692, 602409, 659105, -98371, 1453384]], ![![260161, 826199, 903957, -134915, 1993304]], ![![551588, 1751690, 1916551, -286044, 4226162]], ![![210917, 669814, 732854, -109378, 1616007]]]
  g := ![![![6, 25, -13, 2, -32], ![19, -17, 7, 7, -76], ![14, -56, -44, 41, -50], ![-517, 86, 181, -240, 2078], ![-50, 35, 31, -38, 199]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1427, -172, -1105, 1487, -14770]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![1427, -172, -1105, 1487, -14770]] 
 ![![53, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![40, 0, 0, 0, 1]] where
  M :=![![![1427, -172, -1105, 1487, -14770], ![-5948, -7395, -4533, 4743, -2374], ![-18972, 10650, 23432, -30617, 260850], ![122468, 119410, 57181, -53716, -210686], ![19172, 6340, -4733, 8089, -129643]]]
  hmulB := by decide  
  f := ![![![-281406053105, -893665630004, -977772184929, 145931792901, -2156072680730]], ![![-111895135483, -355347142119, -388790325926, 58026675538, -857316472264]], ![![-75941499710, -241168615362, -263865987526, 39381808195, -581847444474]], ![![-164200090370, -521452810230, -570528882927, 85151024002, -1258065791814]], ![![-215828541020, -685410093192, -749916861399, 111924550317, -1653631881335]]]
  g := ![![![10827, -172, -1105, 1487, -14770], ![3217, -7395, -4533, 4743, -2374], ![-192756, 10650, 23432, -30617, 260850], ![130020, 119410, 57181, -53716, -210686], ![93468, 6340, -4733, 8089, -129643]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-789, 43, 526, -733, 7670]] ![![7, 25, -13, 2, -32]]
  ![![130297, 155500, 92511, -95251, -1164]] where
 M := ![![![130297, 155500, 92511, -95251, -1164]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![130297, 155500, 92511, -95251, -1164]] ![![1427, -172, -1105, 1487, -14770]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![-14181614549, -11568393104, -4122180152, 3205965972, 42056807298]]]
 hmul := by decide  
 g := ![![![![-267577633, -218271568, -77776984, 60489924, 793524666]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1, I53N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
    exact isPrimeI53N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0 ⊙ MulI53N1)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-695, -231, 263, -54, 808]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-695, -231, 263, -54, 808]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![55, 3, 28, 3, 1]] where
  M :=![![![-695, -231, 263, -54, 808], ![216, -103, 199, -221, 1716], ![884, 1048, 66, -191, -2522], ![764, -2402, -2811, 3734, -26210], ![-348, -565, -337, 438, -1447]]]
  hmulB := by decide  
  f := ![![![-359161, -1140593, -1247939, 186254, -2751814]], ![![-745016, -2365959, -2588629, 386351, -5708152]], ![![-1545404, -4907764, -5369654, 801417, -11840554]], ![![-3205668, -10180290, -11138399, 1662398, -24561138]], ![![-1273057, -4042867, -4423358, 660183, -9753889]]]
  g := ![![![-765, -45, -379, -42, 808], ![-1596, -89, -811, -91, 1716], ![2366, 146, 1198, 125, -2522], ![24446, 1292, 12391, 1396, -26210], ![1343, 64, 681, 81, -1447]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 4 2 5 [53, 0, 50, 15, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 30, 57, 4], [46, 26, 31, 36], [44, 2, 30, 19], [0, 1]]
 g := ![![[12, 22, 40, 27], [40, 25, 27, 17], [54, 43, 15], [13, 57, 44, 1], []], ![[44, 37, 44, 13, 32, 35], [42, 56, 8, 35, 21, 49], [54, 12, 1], [46, 18, 6, 2, 27, 9], [9, 55, 5, 27, 6, 5]], ![[34, 46, 4, 4, 38, 41], [2, 37, 48, 37, 23, 51], [41, 17, 20], [13, 8, 33, 10, 12, 41], [50, 40, 21, 12, 9, 46]], ![[6, 20, 54, 32, 35, 45], [30, 28, 45, 56, 25, 4], [41, 30, 51], [13, 36, 19, 25, 53, 5], [21, 22, 7, 31, 51, 15]]]
 h' := ![![[13, 30, 57, 4], [4, 30, 13, 33], [36, 38, 35, 31], [19, 47, 27, 29], [0, 0, 0, 1], [0, 1]], ![[46, 26, 31, 36], [30, 32, 27, 17], [46, 55, 50, 33], [31, 14, 43, 1], [9, 23, 36, 31], [13, 30, 57, 4]], ![[44, 2, 30, 19], [34, 55, 54, 41], [27, 9, 43, 12], [28, 31, 56, 16], [50, 29, 18, 18], [46, 26, 31, 36]], ![[0, 1], [47, 1, 24, 27], [58, 16, 49, 42], [15, 26, 51, 13], [55, 7, 5, 9], [44, 2, 30, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [4, 41, 47], []]
 b := ![[], [], [48, 28, 44, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 4
  hpos := by decide
  P := [53, 0, 50, 15, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![56796447609, 45566851412, 15664509574, -11813099684, -174428782528]
  a := ![-17, 20, 34, -28, 248]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![163565754011, 9641579644, 83045261362, 8669038100, -174428782528]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 12117361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-359161, -1140593, -1247939, 186254, -2751814]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-359161, -1140593, -1247939, 186254, -2751814]] 
 ![![59, 0, 0, 0, 0], ![56, 1, 0, 0, 0], ![50, 0, 1, 0, 0], ![32, 0, 0, 1, 0], ![54, 0, 0, 0, 1]] where
  M :=![![![-359161, -1140593, -1247939, 186254, -2751814], ![-745016, -2365959, -2588629, 386351, -5708152], ![-1545404, -4907764, -5369654, 801417, -11840554], ![-3205668, -10180290, -11138399, 1662398, -24561138], ![-233144, -740399, -810081, 120904, -1786299]]]
  hmulB := by decide  
  f := ![![![-695, -231, 263, -54, 808]], ![![-656, -221, 253, -55, 796]], ![![-574, -178, 224, -49, 642]], ![![-364, -166, 95, 34, -6]], ![![-642, -221, 235, -42, 715]]]
  g := ![![![4551675, -1140593, -1247939, 186254, -2751814], ![9441646, -2365959, -2588629, 386351, -5708152], ![19585028, -4907764, -5369654, 801417, -11840554], ![40625682, -10180290, -11138399, 1662398, -24561138], ![2954652, -740399, -810081, 120904, -1786299]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-695, -231, 263, -54, 808]] ![![-359161, -1140593, -1247939, 186254, -2751814]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![59, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-36508149659, -115939505209, -126851049798, 18932427629, -279717593942]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-36508149659, -115939505209, -126851049798, 18932427629, -279717593942]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![18, 53, 1, 0, 0], ![22, 15, 0, 1, 0], ![8, 45, 0, 0, 1]] where
  M :=![![![-36508149659, -115939505209, -126851049798, 18932427629, -279717593942], ![-75729710516, -240496033085, -263130105748, 39271978370, -580224761170], ![-157087913480, -498866558206, -545816945665, 81462785202, -1203573821560], ![-325851140808, -1034810594232, -1132200883352, 168980164683, -2496601387644], ![-23698721824, -75260403727, -82343470444, 12289703533, -181574511729]]]
  hmulB := by decide  
  f := ![![![111085, 158067, 106990, -115177, 198232]], ![![460708, -151391, -449940, 599820, -5490874]], ![![393734, -128023, -383025, 510808, -4682030]], ![![58794, 105241, 80528, -89779, 273782]], ![![362504, -64918, -294004, 399587, -3896393]]]
  g := ![![![66689149023, 310007728640, -126851049798, 18932427629, -279717593942], ![138334864888, 643056297519, -263130105748, 39271978370, -580224761170], ![286951252566, 1333906750069, -545816945665, 81462785202, -1203573821560], ![595229708814, 2766954036019, -1132200883352, 168980164683, -2496601387644], ![43290268234, 201236901715, -82343470444, 12289703533, -181574511729]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [53, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [33, 60], [0, 1]]
 g := ![![[27, 9], [57], [30, 36], [54, 1], [33, 1]], ![[19, 52], [57], [59, 25], [26, 60], [5, 60]]]
 h' := ![![[33, 60], [45, 58], [57, 22], [5, 55], [20, 60], [0, 1]], ![[0, 1], [7, 3], [51, 39], [51, 6], [48, 1], [33, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [20, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [53, 28, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3094, 11250, 14401, -17162, 115392]
  a := ![-11, 13, 19, -17, 160]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-13244, -93233, 14401, -17162, 115392]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1953, 263, -669, 178, -1862]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![1953, 263, -669, 178, -1862]] 
 ![![61, 0, 0, 0, 0], ![33, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![57, 0, 0, 0, 1]] where
  M :=![![![1953, 263, -669, 178, -1862], ![-712, 803, -353, 125, -848], ![-500, -1060, 830, -255, 2162], ![1020, 642, -683, 198, -1818], ![336, 157, -189, 54, -509]]]
  hmulB := by decide  
  f := ![![![-102087, -324201, -354713, 52942, -782180]], ![![-58699, -186412, -203956, 30441, -449744]], ![![-22263, -70701, -77355, 11545, -170574]], ![![-28324, -89954, -98421, 14690, -217038]], ![![-96479, -306392, -335228, 50034, -739215]]]
  g := ![![![1705, 263, -669, 178, -1862], ![382, 803, -353, 125, -848], ![-1544, -1060, 830, -255, 2162], ![1443, 642, -683, 198, -1818], ![417, 157, -189, 54, -509]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 3, 1, 0, 2]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![-1, 3, 1, 0, 2]] 
 ![![61, 0, 0, 0, 0], ![47, 1, 0, 0, 0], ![48, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![27, 0, 0, 0, 1]] where
  M :=![![![-1, 3, 1, 0, 2], ![0, 1, 5, -1, 12], ![4, 8, 6, -1, 14], ![4, 14, 15, -2, 26], ![0, 1, 1, 0, 1]]]
  hmulB := by decide  
  f := ![![![-25, -5, 13, -4, 32]], ![![-19, -4, 10, -3, 24]], ![![-20, -4, 10, -3, 26]], ![![-1, 1, 2, -2, 14]], ![![-11, -2, 6, -2, 15]]]
  g := ![![![-4, 3, 1, 0, 2], ![-10, 1, 5, -1, 12], ![-17, 8, 6, -1, 14], ![-34, 14, 15, -2, 26], ![-2, 1, 1, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2

def I61N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21, 3, 4, -1, 10]] i)))

def SI61N3: IdealEqSpanCertificate' Table ![![-21, 3, 4, -1, 10]] 
 ![![61, 0, 0, 0, 0], ![50, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![11, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![-21, 3, 4, -1, 10], ![4, -15, 6, 0, 2], ![0, 6, -13, 4, 12], ![-16, 28, 46, -49, 304], ![0, 5, 6, -5, 13]]]
  hmulB := by decide  
  f := ![![![17011, 54031, 59116, -8823, 130356]], ![![14522, 46125, 50466, -7532, 111282]], ![![1479, 4697, 5139, -767, 11332]], ![![5557, 17649, 19310, -2882, 42580]], ![![2412, 7661, 8382, -1251, 18483]]]
  g := ![![![-4, 3, 4, -1, 10], ![12, -15, 6, 0, 2], ![-7, 6, -13, 4, 12], ![-55, 28, 46, -49, 304], ![-5, 5, 6, -5, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N3 : Nat.card (O ⧸ I61N3) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N3)

lemma isPrimeI61N3 : Ideal.IsPrime I61N3 := prime_ideal_of_norm_prime hp61.out _ NI61N3
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-36508149659, -115939505209, -126851049798, 18932427629, -279717593942]] ![![1953, 263, -669, 178, -1862]]
  ![![940849, 3031660, 3312739, -494263, 7305970]] where
 M := ![![![940849, 3031660, 3312739, -494263, 7305970]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![940849, 3031660, 3312739, -494263, 7305970]] ![![-1, 3, 1, 0, 2]]
  ![![10333055, 32742407, 35867608, -5355873, 79095096]] where
 M := ![![![10333055, 32742407, 35867608, -5355873, 79095096]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI61N2 : IdealMulLeCertificate' Table 
  ![![10333055, 32742407, 35867608, -5355873, 79095096]] ![![-21, 3, 4, -1, 10]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![-330559, 579744, -291824, 99674, -722484]]]
 hmul := by decide  
 g := ![![![![-5419, 9504, -4784, 1634, -11844]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1, I61N2, I61N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
    exact isPrimeI61N2
    exact isPrimeI61N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0 ⊙ MulI61N1 ⊙ MulI61N2)


lemma PB532I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB532I1 : PrimesBelowBoundCertificateInterval O 23 61 532 where
  m := 9
  g := ![4, 1, 3, 1, 1, 2, 3, 2, 4]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB532I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1, I29N2, I29N3]
    · exact ![I31N0]
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1, I61N2, I61N3]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC29
    · exact PBC31
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![841, 29, 29, 29]
    · exact ![28629151]
    · exact ![1369, 1369, 37]
    · exact ![115856201]
    · exact ![147008443]
    · exact ![4879681, 47]
    · exact ![148877, 53, 53]
    · exact ![12117361, 59]
    · exact ![3721, 61, 61, 61]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
      exact NI29N2
      exact NI29N3
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
      exact NI37N2
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
      exact NI53N2
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
      exact NI61N2
      exact NI61N3
  β := ![I29N1, I29N2, I29N3, I37N2, I47N1, I53N1, I53N2, I59N1, I61N1, I61N2, I61N3]
  Il := ![[I29N1, I29N2, I29N3], [], [I37N2], [], [], [I47N1], [I53N1, I53N2], [I59N1], [I61N1, I61N2, I61N3]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
