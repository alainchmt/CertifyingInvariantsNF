
import IdealArithmetic.Examples.NF5_3_2025000000_1.RI5_3_2025000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0, 0, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0, 0, 0]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![0, 0, 0, 0, 29]] where
  M :=![![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![0, 0, 0, 0, 29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 5 2 4 [16, 15, 12, 15, 19, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 23, 27, 25, 2], [9, 11, 26, 3, 17], [1, 20, 1, 6, 26], [3, 3, 4, 24, 13], [0, 1]]
 g := ![![[2, 20, 26, 14, 6], [19, 12, 0, 6], [27, 10, 1], []], ![[12, 18, 22, 13, 19, 19, 19, 27], [1, 14, 7, 4], [16, 16, 4, 15, 24, 1, 10, 21], [10, 0, 3, 19, 16, 11, 3, 8]], ![[0, 18, 27, 28, 11, 8, 13, 2], [7, 16, 9, 13], [9, 27, 6, 21, 26, 15, 20, 18], [1, 3, 2, 6, 24, 6, 24, 12]], ![[20, 13, 18, 18, 18, 8, 27, 2], [16, 7, 0, 16], [5, 10, 14, 25, 7, 3, 22, 19], [24, 8, 8, 10, 6, 14, 8, 2]], ![[15, 4, 12, 18, 2, 3, 15, 4], [14, 24, 6, 23], [28, 25, 22, 16, 3, 18, 27, 25], [22, 27, 11, 8, 18, 26, 5, 22]]]
 h' := ![![[26, 23, 27, 25, 2], [24, 19, 9, 8, 8], [3, 15, 3, 11, 21], [0, 0, 0, 1], [0, 1]], ![[9, 11, 26, 3, 17], [7, 3, 6, 18, 17], [20, 22, 8, 28, 2], [16, 7, 5, 5, 24], [26, 23, 27, 25, 2]], ![[1, 20, 1, 6, 26], [10, 13, 17, 26, 13], [21, 2, 8, 22, 19], [17, 0, 13, 14, 10], [9, 11, 26, 3, 17]], ![[3, 3, 4, 24, 13], [27, 1, 17, 28, 26], [14, 24, 1, 20, 25], [23, 7, 0, 7, 10], [1, 20, 1, 6, 26]], ![[0, 1], [14, 22, 9, 7, 23], [8, 24, 9, 6, 20], [23, 15, 11, 2, 14], [3, 3, 4, 24, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 1, 28, 28], [], [], []]
 b := ![[], [23, 11, 10, 11, 15], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 5
  hpos := by decide
  P := [16, 15, 12, 15, 19, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![974548906257080, -648550331731079, -1417131878193673, -798950043872186, -2778966700850498]
  a := ![35, 19, 2, -11, -85]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![33605134698520, -22363804542451, -48866616489437, -27550001512834, -95826437960362]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 20511149 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def PBC29 : ContainsPrimesAboveP 29 ![I29N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![29, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 29 (by decide) 𝕀

instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2564251, 3157635, 537221, -122346, -1150354]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![2564251, 3157635, 537221, -122346, -1150354]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![27, 30, 17, 24, 1]] where
  M :=![![![2564251, 3157635, 537221, -122346, -1150354], ![-587864, -1058397, -171081, 47837, 441652], ![213586, 796048, 218722, 20267, -140150], ![-564038, -509150, 355331, 299790, 1249678], ![940254, 1194374, 232057, -28075, -368131]]]
  hmulB := by decide  
  f := ![![![1126067, 2168861, 1580515, -198772, -2193252]], ![![-1603696, -6056765, -4212123, 785427, 2014760]], ![![-6966458, 171928, -797912, -1070415, 18645478]], ![![52276766, 76178774, 57178777, -5079572, -110976022]], ![![35735495, 54459909, 40662698, -3876052, -74970149]]]
  g := ![![![1084639, 1215105, 648169, 886650, -1150354], ![-403628, -461547, -247715, -340381, 441652], ![128956, 161308, 83912, 109157, -140150], ![-1106624, -1225790, -673845, -957822, 1249678], ![350961, 394784, 209364, 284099, -368131]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 4 2 4 [25, 26, 11, 26, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 20, 17, 1], [15, 14, 3, 19], [28, 27, 11, 11], [0, 1]]
 g := ![![[4, 25, 14, 18], [1, 22, 12, 2], [20, 14, 5, 1], []], ![[24, 15, 23, 0, 4, 1], [27, 29, 2, 5, 24, 19], [12, 28, 15, 29, 12, 28], [18, 28, 25, 18, 25, 1]], ![[6, 28, 19, 11, 11, 25], [3, 12, 21, 15, 11, 8], [10, 5, 15, 26, 23, 28], [7, 2, 1, 9, 3, 8]], ![[25, 11, 29, 22, 12, 21], [24, 11, 17, 3, 17, 27], [2, 11, 21, 9, 14, 27], [28, 23, 30, 3, 15, 29]]]
 h' := ![![[24, 20, 17, 1], [6, 29, 1, 24], [27, 29, 4, 8], [0, 0, 0, 1], [0, 1]], ![[15, 14, 3, 19], [18, 26, 9, 30], [5, 1, 16, 9], [13, 5, 19, 20], [24, 20, 17, 1]], ![[28, 27, 11, 11], [4, 29, 23, 4], [20, 7, 28, 19], [7, 11, 27, 15], [15, 14, 3, 19]], ![[0, 1], [9, 9, 29, 4], [13, 25, 14, 26], [17, 15, 16, 26], [28, 27, 11, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [4, 0, 2], []]
 b := ![[], [], [12, 24, 16, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 4
  hpos := by decide
  P := [25, 26, 11, 26, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-50384779261, 33429882230, 73179648122, 41275755634, 143637685018]
  a := ![-27, -79, -1, 8, 66]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-126729105637, -137925828010, -76408419264, -109871893058, 143637685018]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 923521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1126067, -2168861, -1580515, 198772, 2193252]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-1126067, -2168861, -1580515, 198772, 2193252]] 
 ![![31, 0, 0, 0, 0], ![25, 1, 0, 0, 0], ![26, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![30, 0, 0, 0, 1]] where
  M :=![![![-1126067, -2168861, -1580515, 198772, 2193252], ![1603696, 6056765, 4212123, -785427, -2014760], ![6966458, -171928, 797912, 1070415, -18645478], ![-52276766, -76178774, -57178777, 5079572, 110976022], ![10705182, 19812470, 14492721, -1753205, -21151787]]]
  hmulB := by decide  
  f := ![![![-2564251, -3157635, -537221, 122346, 1150354]], ![![-2048981, -2512338, -427724, 97123, 913458]], ![![-2157552, -2674018, -457628, 101959, 969334]], ![![-64523, -85435, -28792, -5724, -3204]], ![![-2511864, -3094304, -527377, 119305, 1125121]]]
  g := ![![![909436, -2168861, -1580515, 198772, 2193252], ![-6390400, 6056765, 4212123, -785427, -2014760], ![17703641, -171928, 797912, 1070415, -18645478], ![144534, -76178774, -57178777, 5079572, 110976022], ![-7261629, 19812470, 14492721, -1753205, -21151787]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![2564251, 3157635, 537221, -122346, -1150354]] ![![-1126067, -2168861, -1580515, 198772, 2193252]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![-31, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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
instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0, 0, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0, 0, 0]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]] where
  M :=![![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 5 2 5 [35, 28, 12, 10, 31, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 0, 5, 16, 26], [25, 26, 7, 10, 15], [4, 15, 9, 36, 36], [16, 32, 16, 12, 34], [0, 1]]
 g := ![![[36, 9, 33, 10, 12], [33, 35, 18, 26], [33, 10, 26, 6, 1], [], []], ![[10, 17, 28, 9, 31, 27, 29, 11], [19, 21, 3, 27], [27, 6, 28, 31, 14, 5, 30, 26], [33, 31, 33, 12], [13, 33, 4, 10]], ![[7, 19, 25, 9, 24, 3, 32, 14], [6, 17, 0, 16], [28, 32, 17, 33, 16, 16, 28, 14], [26, 9, 5, 34], [28, 5, 22, 3]], ![[31, 28, 18, 28, 31, 27, 13, 11], [29, 32, 1, 33], [21, 26, 8, 2, 1, 11, 1, 26], [21, 13, 19, 25], [23, 21, 8, 1]], ![[31, 31, 25, 35, 2, 25, 16, 28], [30, 18, 27, 4], [28, 31, 9, 36, 12, 36, 16, 16], [5, 18, 9, 28], [30, 35, 19, 9]]]
 h' := ![![[35, 0, 5, 16, 26], [19, 31, 20, 15, 30], [29, 21, 5, 18, 27], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[25, 26, 7, 10, 15], [4, 20, 11, 36, 31], [22, 20, 2, 3, 29], [4, 17, 34, 30, 1], [30, 35, 18, 21, 7], [35, 0, 5, 16, 26]], ![[4, 15, 9, 36, 36], [9, 17, 18, 21, 25], [16, 29, 18, 25, 4], [18, 11, 14, 9, 12], [15, 8, 2, 25, 16], [25, 26, 7, 10, 15]], ![[16, 32, 16, 12, 34], [28, 18, 6, 18, 10], [9, 22, 26, 18, 12], [1, 17, 30, 21, 14], [25, 36, 4, 2, 32], [4, 15, 9, 36, 36]], ![[0, 1], [26, 25, 19, 21, 15], [15, 19, 23, 10, 2], [3, 29, 33, 14, 9], [20, 32, 12, 26, 19], [16, 32, 16, 12, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24, 27, 10, 2], [], [], []]
 b := ![[], [31, 16, 8, 1, 17], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 5
  hpos := by decide
  P := [35, 28, 12, 10, 31, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5621941853947, -3744984089696, -8179488381720, -4610204089092, -16032453603080]
  a := ![12, 4, 1, -4, -29]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![151944374431, -101215786208, -221067253560, -124600110516, -433309556840]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 69343957 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def PBC37 : ContainsPrimesAboveP 37 ![I37N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![37, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 37 (by decide) 𝕀

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


def P41P0 : CertificateIrreducibleZModOfList' 41 5 2 5 [40, 33, 24, 6, 14, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 7, 12, 4, 24], [18, 19, 13, 2, 3], [38, 21, 38, 40, 2], [13, 34, 19, 36, 12], [0, 1]]
 g := ![![[40, 15, 32, 36, 1], [25, 26, 38, 1], [3, 8, 7, 32], [1], []], ![[16, 35, 39, 24, 39, 39, 15, 14], [7, 3, 18, 5], [8, 13, 11, 21], [37, 24, 37, 0, 10, 2, 12, 17], [13, 6, 0, 2]], ![[34, 10, 5, 8, 21, 33, 40, 15], [24, 20, 25, 31], [13, 36, 18, 39], [28, 23, 31, 36, 40, 18, 22, 17], [38, 25, 9, 9]], ![[32, 12, 38, 14, 23, 33, 13, 21], [34, 39, 35, 2], [23, 37, 10, 10], [21, 20, 33, 35, 37, 19, 28, 4], [31, 26, 22, 4]], ![[30, 40, 12, 37, 26, 37, 18, 22], [6, 31, 21, 40], [25, 16, 18, 18], [5, 2, 33, 37, 2, 36, 14, 15], [9, 1, 37, 21]]]
 h' := ![![[40, 7, 12, 4, 24], [0, 36, 20, 25, 1], [4, 7, 15, 15, 40], [1, 8, 17, 35, 27], [0, 0, 1], [0, 1]], ![[18, 19, 13, 2, 3], [30, 9, 21, 30, 39], [33, 39, 9, 16, 13], [5, 29, 27, 30, 29], [14, 14, 7, 22, 32], [40, 7, 12, 4, 24]], ![[38, 21, 38, 40, 2], [8, 40, 18, 19, 28], [36, 9, 0, 8, 21], [8, 20, 1, 7, 11], [34, 29, 3, 24, 19], [18, 19, 13, 2, 3]], ![[13, 34, 19, 36, 12], [26, 31, 31, 36, 20], [19, 25, 28, 32, 17], [18, 31, 39, 3, 25], [40, 25, 27, 29, 17], [38, 21, 38, 40, 2]], ![[0, 1], [2, 7, 33, 13, 35], [23, 2, 30, 11, 32], [11, 35, 39, 7, 31], [14, 14, 3, 7, 14], [13, 34, 19, 36, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32, 20, 13, 15], [], [], []]
 b := ![[], [8, 18, 20, 19, 25], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 5
  hpos := by decide
  P := [40, 33, 24, 6, 14, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4591409163968362, 3041168514814668, 6661710324469856, 3761473625311950, 13087531196885784]
  a := ![-51, -10, -3, 14, 124]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-111985589365082, 74174841824748, 162480739621216, 91743259153950, 319208077972824]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5138573, 4780704, 3831425, -41069, -11919854]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![5138573, 4780704, 3831425, -41069, -11919854]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![29, 34, 42, 42, 1]] where
  M :=![![![5138573, 4780704, 3831425, -41069, -11919854], ![-23264742, -42212291, -30937789, 3667149, 46283070], ![41226054, 132530346, 92969770, -16269193, -60449214], ![106870274, -70417258, -32548103, 27892998, -311355706], ![-44519010, -35831342, -29502281, -589855, 105357205]]]
  hmulB := by decide  
  f := ![![![-3799373, -4027052, -672155, 162097, 1432602]], ![![595846, 634259, 108657, -23767, -219110]], ![![-105482, -90458, 696, 13589, 68362]], ![![-53522, 59254, 101039, 55052, 188578]], ![![-2279857, -2280028, -273758, 159074, 1056703]]]
  g := ![![![8158473, 9536180, 11731751, 11641693, -11919854], ![-31755204, -37577597, -45926203, -45121437, 46283070], ![41726820, 50879154, 61205506, 58665065, -60449214], ![212469436, 244550622, 303357943, 304763550, -311355706], ![-72090185, -84138984, -103593137, -102920755, 105357205]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 4 2 5 [12, 25, 20, 25, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 18, 2, 32], [40, 12, 4, 29], [9, 12, 37, 25], [0, 1]]
 g := ![![[42, 2, 40, 4], [2, 25, 18, 35], [12, 2, 9], [18, 1], []], ![[17, 8, 34, 26, 1, 12], [28, 4, 17, 40, 33, 42], [38, 14, 41], [18, 5, 16, 10, 35, 42], [39, 27, 35]], ![[36, 13, 39, 26], [9, 42, 32, 16, 27, 19], [4, 2, 10], [12, 13, 5, 21, 40, 8], [15, 19, 24]], ![[19, 40, 4, 40, 27, 21], [21, 42, 30, 13, 34, 10], [27, 11, 10], [30, 27, 5, 33, 31, 36], [35, 28, 23]]]
 h' := ![![[12, 18, 2, 32], [19, 18, 35, 2], [29, 41, 20, 32], [42, 11, 2, 3], [0, 0, 1], [0, 1]], ![[40, 12, 4, 29], [7, 12, 7, 34], [5, 42, 0, 41], [26, 19, 28, 27], [20, 36, 2, 41], [12, 18, 2, 32]], ![[9, 12, 37, 25], [38, 17, 32], [18, 6, 11, 10], [25, 37, 26, 28], [1, 13, 3, 29], [40, 12, 4, 29]], ![[0, 1], [22, 39, 12, 7], [13, 40, 12, 3], [37, 19, 30, 28], [5, 37, 37, 16], [9, 12, 37, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [35, 0, 19], []]
 b := ![[], [], [25, 25, 33, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 4
  hpos := by decide
  P := [12, 25, 20, 25, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2213672679025, 1544501294370, 3298684548105, 1833487424016, 6337198441980]
  a := ![65, 37, 5, -17, -158]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4325405290615, -4974889435650, -6113108139885, -6147182491608, 6337198441980]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 3418801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3799373, -4027052, -672155, 162097, 1432602]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-3799373, -4027052, -672155, 162097, 1432602]] 
 ![![43, 0, 0, 0, 0], ![38, 1, 0, 0, 0], ![18, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![37, 0, 0, 0, 1]] where
  M :=![![![-3799373, -4027052, -672155, 162097, 1432602], ![595846, 634259, 108657, -23767, -219110], ![-105482, -90458, 696, 13589, 68362], ![-53522, 59254, 101039, 55052, 188578], ![-1432630, -1510934, -246307, 64525, 551031]]]
  hmulB := by decide  
  f := ![![![5138573, 4780704, 3831425, -41069, -11919854]], ![![4000024, 3243127, 2666427, 48989, -9457474]], ![![3109776, 5083326, 3765940, -395545, -6395502]], ![![2963362, -1192894, -400521, 644854, -8349654]], ![![3386237, 3280342, 2610708, -49056, -7806451]]]
  g := ![![![2504017, -4027052, -672155, 162097, 1432602], ![-401388, 634259, 108657, -23767, -219110], ![17108, -90458, 696, 13589, 68362], ![-263290, 59254, 101039, 55052, 188578], ![924887, -1510934, -246307, 64525, 551031]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![5138573, 4780704, 3831425, -41069, -11919854]] ![![-3799373, -4027052, -672155, 162097, 1432602]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![43, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3096895, -10140712, -1811327, 359447, 4127400]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-3096895, -10140712, -1811327, 359447, 4127400]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![29, 8, 6, 38, 1]] where
  M :=![![![-3096895, -10140712, -1811327, 359447, 4127400], ![3222542, 10537129, 1882041, -373539, -4288402], ![-3347258, -10942754, -1954538, 387885, 4453282], ![3476174, 11362790, 2029207, -402998, -4625038], ![-1130478, -3701966, -661263, 131207, 1506707]]]
  hmulB := by decide  
  f := ![![![4499, 6756, 5053, -471, -9476]], ![![-12358, -29637, -21201, 3169, 21890]], ![![-586, 49850, 32864, -8525, 20186]], ![![159722, 148358, 118933, -1236, -370594]], ![![128859, 124186, 98922, -1758, -297305]]]
  g := ![![![-2612585, -918296, -565441, -3329399, 4127400], ![2714600, 954135, 587499, 3459271, -4288402], ![-2818988, -990830, -610090, -3592273, 4453282], ![2927708, 1029002, 633605, 3730818, -4625038], ![-953723, -335226, -206415, -1215397, 1506707]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 4 2 5 [28, 13, 42, 37, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 7, 29, 20], [20, 18, 14, 3], [36, 21, 4, 24], [0, 1]]
 g := ![![[5, 37, 15, 42], [39, 43, 43, 16], [39, 32, 3, 27], [10, 1], []], ![[23, 13, 19, 40, 0, 5], [45, 23, 16, 7, 42, 40], [34, 8, 37, 7, 28, 33], [23, 31, 42, 21, 22, 31], [13, 37, 24]], ![[5, 19, 32, 27, 24, 21], [19, 4, 37, 30, 2, 4], [39, 7, 15, 3, 5, 37], [7, 38, 46, 10, 36, 34], [21, 33, 9]], ![[6, 18, 46, 21, 35, 7], [42, 35, 27, 0, 40, 16], [6, 12, 5, 31, 21, 8], [26, 27, 33, 8, 29, 42], [21, 30, 12]]]
 h' := ![![[1, 7, 29, 20], [36, 8, 23, 29], [36, 11, 3, 4], [2, 30, 37, 11], [0, 0, 1], [0, 1]], ![[20, 18, 14, 3], [37, 8, 34, 23], [13, 31, 20, 7], [42, 23, 44, 45], [13, 31, 6, 26], [1, 7, 29, 20]], ![[36, 21, 4, 24], [32, 17, 35, 17], [0, 18, 6, 8], [39, 20, 32, 34], [0, 40, 26, 36], [20, 18, 14, 3]], ![[0, 1], [41, 14, 2, 25], [44, 34, 18, 28], [19, 21, 28, 4], [3, 23, 14, 32], [36, 21, 4, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [1, 41, 14], []]
 b := ![[], [], [1, 21, 13, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 4
  hpos := by decide
  P := [28, 13, 42, 37, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9045925190, -1825847448, 18376507462, 18575398106, 22279335822]
  a := ![-42, -24, -2, 2, 102]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-13939290724, -3831075192, -2453181010, -17617858790, 22279335822]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 4879681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4499, -6756, -5053, 471, 9476]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-4499, -6756, -5053, 471, 9476]] 
 ![![47, 0, 0, 0, 0], ![28, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![19, 0, 0, 0, 1]] where
  M :=![![![-4499, -6756, -5053, 471, 9476], ![12358, 29637, 21201, -3169, -21890], ![586, -49850, -32864, 8525, -20186], ![-159722, -148358, -118933, 1236, 370594], ![41154, 58790, 44233, -3799, -87805]]]
  hmulB := by decide  
  f := ![![![3096895, 10140712, 1811327, -359447, -4127400]], ![![1776394, 5817081, 1039045, -206191, -2367634]], ![![1059589, 3469222, 619669, -122970, -1412006]], ![![123713, 405518, 72442, -14369, -165046]], ![![1275989, 4178202, 746308, -148100, -1700581]]]
  g := ![![![1681, -6756, -5053, 471, 9476], ![-15108, 29637, 21201, -3169, -21890], ![47815, -49850, -32864, 8525, -20186], ![-26951, -148358, -118933, 1236, 370594], ![-12527, 58790, 44233, -3799, -87805]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-3096895, -10140712, -1811327, 359447, 4127400]] ![![-4499, -6756, -5053, 471, 9476]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8315, 8813, 1469, -356, -3140]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![8315, 8813, 1469, -356, -3140]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![21, 30, 1, 0, 0], ![6, 22, 0, 1, 0], ![28, 10, 0, 0, 1]] where
  M :=![![![8315, 8813, 1469, -356, -3140], ![-1296, -1397, -251, 45, 456], ![282, 168, -74, -71, -294], ![406, -326, -643, -358, -1238], ![3154, 3294, 511, -157, -1261]]]
  hmulB := by decide  
  f := ![![![329, 1129, 173, -38, -414]], ![![-296, -1023, -75, 21, 364]], ![![-29, -113, 27, -3, 28]], ![![-116, -346, -35, 6, 166]], ![![126, 420, 85, -17, -165]]]
  g := ![![![1274, 75, 1469, -356, -3140], ![-171, 11, -251, 45, 456], ![198, 130, -74, -71, -294], ![957, 740, -643, -358, -1238], ![541, 76, 511, -157, -1261]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [51, 48, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 52], [0, 1]]
 g := ![![[29, 47], [52], [42, 4], [40], [5, 1]], ![[52, 6], [52], [9, 49], [40], [10, 52]]]
 h' := ![![[5, 52], [5, 43], [31, 23], [21, 51], [10, 27], [0, 1]], ![[0, 1], [8, 10], [40, 30], [11, 2], [39, 26], [5, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [13, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [51, 48, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7724, 1188, 2392, 1796, -19976]
  a := ![23, 14, 4, 0, -54]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![9548, 1692, 2392, 1796, -19976]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-151, 38, 5, -29, 418]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-151, 38, 5, -29, 418]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![13, 51, 1, 0, 0], ![26, 9, 0, 1, 0], ![34, 28, 0, 0, 1]] where
  M :=![![![-151, 38, 5, -29, 418], ![1242, 1753, 1321, -111, -2658], ![-3762, -8502, -6110, 877, 6858], ![1438, 16654, 11195, -2602, 2386], ![1162, -846, -407, 317, -3415]]]
  hmulB := by decide  
  f := ![![![-211903, -693146, -123805, 24571, 282102]], ![![220210, 719937, 128589, -25521, -292994]], ![![155609, 508647, 90850, -18031, -207002]], ![![-62078, -203133, -36282, 7201, 82676]], ![![-21060, -69090, -12341, 2449, 28125]]]
  g := ![![![-258, -220, 5, -29, 418], ![1459, 185, 1321, -111, -2658], ![-3402, 1947, -6110, 877, 6858], ![-2973, -11277, 11195, -2602, 2386], ![2157, 2126, -407, 317, -3415]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P1 : CertificateIrreducibleZModOfList' 53 2 2 5 [46, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14, 52], [0, 1]]
 g := ![![[2, 15], [40], [20, 36], [28], [14, 1]], ![[0, 38], [40], [47, 17], [28], [28, 52]]]
 h' := ![![[14, 52], [5, 11], [34, 27], [48, 6], [45, 44], [0, 1]], ![[0, 1], [0, 42], [41, 26], [26, 47], [25, 9], [14, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [10, 44]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N1 : CertifiedPrimeIdeal' SI53N1 53 where
  n := 2
  hpos := by decide
  P := [46, 39, 1]
  hirr := P53P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3524, 6338, 11182, 5180, 11516]
  a := ![-19, -14, -1, 4, 46]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-12738, -17604, 11182, 5180, 11516]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N1 B_one_repr
lemma NI53N1 : Nat.card (O ⧸ I53N1) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![445, 472, 79, -19, -168]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![445, 472, 79, -19, -168]] 
 ![![53, 0, 0, 0, 0], ![25, 1, 0, 0, 0], ![11, 0, 1, 0, 0], ![43, 0, 0, 1, 0], ![19, 0, 0, 0, 1]] where
  M :=![![![445, 472, 79, -19, -168], ![-70, -75, -13, 3, 26], ![10, 10, 0, -1, -2], ![10, 10, 5, -4, -26], ![166, 174, 27, -7, -61]]]
  hmulB := by decide  
  f := ![![![-4771, -15596, -2787, 553, 6348]], ![![-2157, -7051, -1260, 250, 2870]], ![![-1087, -3554, -635, 126, 1446]], ![![-3771, -12326, -2204, 437, 5018]], ![![-1743, -5698, -1018, 202, 2319]]]
  g := ![![![-155, 472, 79, -19, -168], ![25, -75, -13, 3, 26], ![-3, 10, 0, -1, -2], ![7, 10, 5, -4, -26], ![-57, 174, 27, -7, -61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![8315, 8813, 1469, -356, -3140]] ![![-151, 38, 5, -29, 418]]
  ![![3195, 3337, 518, -133, -1198]] where
 M := ![![![3195, 3337, 518, -133, -1198]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![3195, 3337, 518, -133, -1198]] ![![445, 472, 79, -19, -168]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![993167, 1053163, 176013, -42294, -374498]]]
 hmul := by decide  
 g := ![![![![18739, 19871, 3321, -798, -7066]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-255918939, -271365371, -45327045, 10902180, 96467800]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-255918939, -271365371, -45327045, 10902180, 96467800]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![25, 37, 1, 0, 0], ![19, 13, 0, 1, 0], ![51, 43, 0, 0, 1]] where
  M :=![![![-255918939, -271365371, -45327045, 10902180, 96467800], ![40305080, 42734821, 7135849, -1718325, -15197080], ![-6337610, -6736640, -1138094, 262549, 2365270], ![1054854, 1023078, 96621, -87898, -534414], ![-96200582, -102013094, -17044373, 4095385, 36253665]]]
  hmulB := by decide  
  f := ![![![320337, 661463, 478985, -64070, -607306]], ![![-317632, -1596327, -1096385, 222705, 250844]], ![![-107799, -739380, -502680, 109030, 11308]], ![![304615, 290140, 231579, -3575, -704092]], ![![-6845, -695214, -460293, 116646, -241461]]]
  g := ![![![-72029526, -48883194, -45327045, 10902180, 96467800], ![11349290, 7703747, 7135849, -1718325, -15197080], ![-1754279, -1182151, -1138094, 262549, 2365270], ![467195, 365603, 96621, -87898, -534414], ![-27065093, -18364727, -17044373, 4095385, 36253665]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [36, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [58, 58], [0, 1]]
 g := ![![[41, 41], [3, 3], [1], [31, 45], [58, 1]], ![[0, 18], [0, 56], [1], [45, 14], [57, 58]]]
 h' := ![![[58, 58], [10, 10], [48, 48], [5, 58], [36, 24], [0, 1]], ![[0, 1], [0, 49], [0, 11], [6, 1], [12, 35], [58, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [26, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [36, 1, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-36744, 69831, 115478, 52601, 120024]
  a := ![-55, -31, 0, 13, 134]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-170243, -170300, 115478, 52601, 120024]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-338589, -634968, -463887, 56861, 665888]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-338589, -634968, -463887, 56861, 665888]] 
 ![![59, 0, 0, 0, 0], ![43, 1, 0, 0, 0], ![39, 0, 1, 0, 0], ![34, 0, 0, 1, 0], ![35, 0, 0, 0, 1]] where
  M :=![![![-338589, -634968, -463887, 56861, 665888], ![535722, 1870075, 1305835, -236443, -730278], ![1849646, -493846, -84316, 360063, -5117950], ![-15276782, -21502658, -16207759, 1355936, 32713942], ![3204326, 5774098, 4234771, -498329, -6389631]]]
  hmulB := by decide  
  f := ![![![16954997, 55430620, 9897361, -1966977, -22566468]], ![![12058807, 39422739, 7038724, -1399162, -16050330]], ![![11518811, 37652846, 6721331, -1337222, -15332974]], ![![9456600, 30885850, 5504379, -1102572, -12598354]], ![![10163459, 33225218, 5931828, -1179432, -13527947]]]
  g := ![![![335886, -634968, -463887, 56861, 665888], ![-1647564, 1870075, 1305835, -236443, -730278], ![3275584, -493846, -84316, 360063, -5117950], ![5938141, -21502658, -16207759, 1355936, 32713942], ![-2875554, 5774098, 4234771, -498329, -6389631]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-85, -4675, -3097, 778, -1520]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![-85, -4675, -3097, 778, -1520]] 
 ![![59, 0, 0, 0, 0], ![47, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![42, 0, 0, 1, 0], ![51, 0, 0, 0, 1]] where
  M :=![![![-85, -4675, -3097, 778, -1520], ![-13932, -12389, -10013, 15, 32532], ![64854, 116076, 85192, -9953, -129618], ![-119894, -373994, -262825, 45380, 180070], ![4606, 49554, 33349, -7699, 6227]]]
  hmulB := by decide  
  f := ![![![-3153830377, -3344179217, -558584431, 134356336, 1188834738]], ![![-2503955033, -2655080768, -443483044, 106670995, 943864562]], ![![-1765332581, -1871878895, -312663387, 75204939, 665441212]], ![![-2244890812, -2380380760, -397599383, 95634606, 846210458]], ![![-2746286883, -2912038511, -486403170, 116994575, 1035211429]]]
  g := ![![![6215, -4675, -3097, 778, -1520], ![-12898, -12389, -10013, 15, 32532], ![-19890, 116076, 85192, -9953, -129618], ![254941, -373994, -262825, 45380, 180070], ![-57952, 49554, 33349, -7699, 6227]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2

def I59N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1861395, -6081948, -1086279, 215611, 2475110]] i)))

def SI59N3: IdealEqSpanCertificate' Table ![![-1861395, -6081948, -1086279, 215611, 2475110]] 
 ![![59, 0, 0, 0, 0], ![50, 1, 0, 0, 0], ![37, 0, 1, 0, 0], ![38, 0, 0, 1, 0], ![51, 0, 0, 0, 1]] where
  M :=![![![-1861395, -6081948, -1086279, 215611, 2475110], ![1931666, 6314157, 1127771, -223835, -2569666], ![-2005642, -6556318, -1171006, 232431, 2668274], ![2082514, 6808006, 1216073, -241282, -2770442], ![-679554, -2220334, -396561, 78717, 903601]]]
  hmulB := by decide  
  f := ![![![61603, 359688, 245741, -51671, -29938]], ![![63452, 310841, 213705, -43127, -53118]], ![![-26129, 120530, 76227, -24306, 114720]], ![![193296, 636098, 445623, -78770, -277934]], ![![39865, 248966, 169732, -36180, -13321]]]
  g := ![![![3525500, -6081948, -1086279, 215611, 2475110], ![-3660085, 6314157, 1127771, -223835, -2569666], ![3800392, -6556318, -1171006, 232431, 2668274], ![-3946631, 6808006, 1216073, -241282, -2770442], ![1287034, -2220334, -396561, 78717, 903601]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N3 : Nat.card (O ⧸ I59N3) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N3)

lemma isPrimeI59N3 : Ideal.IsPrime I59N3 := prime_ideal_of_norm_prime hp59.out _ NI59N3
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-255918939, -271365371, -45327045, 10902180, 96467800]] ![![-338589, -634968, -463887, 56861, 665888]]
  ![![3396179, 3601157, 601508, -144681, -1280184]] where
 M := ![![![3396179, 3601157, 601508, -144681, -1280184]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![3396179, 3601157, 601508, -144681, -1280184]] ![![-85, -4675, -3097, 778, -1520]]
  ![![61603, 359688, 245741, -51671, -29938]] where
 M := ![![![61603, 359688, 245741, -51671, -29938]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI59N2 : IdealMulLeCertificate' Table 
  ![![61603, 359688, 245741, -51671, -29938]] ![![-1861395, -6081948, -1086279, 215611, 2475110]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![59, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1, I59N2, I59N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
    exact isPrimeI59N2
    exact isPrimeI59N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0 ⊙ MulI59N1 ⊙ MulI59N2)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-421, -1329, -868, 151, 622]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-421, -1329, -868, 151, 622]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![40, 16, 1, 0, 0], ![31, 28, 0, 1, 0], ![18, 8, 0, 0, 1]] where
  M :=![![![-421, -1329, -868, 151, 622], ![-870, 859, 386, -264, 2646], ![8988, 11826, 9061, -670, -19560], ![-29740, -63892, -46184, 6381, 55460], ![4020, 11668, 8260, -1378, -6365]]]
  hmulB := by decide  
  f := ![![![1924441, 2040643, 340894, -81959, -725340]], ![![-303254, -321247, -53418, 13058, 114754]], ![![1183152, 1254706, 209689, -50338, -445780]], ![![838575, 889525, 148842, -35572, -315616]], ![![539950, 572606, 95696, -22972, -203437]]]
  g := ![![![302, 55, -868, 151, 622], ![-914, -313, 386, -264, 2646], ![318, 690, 9061, -670, -19560], ![10189, 864, -46184, 6381, 55460], ![-2772, -508, 8260, -1378, -6365]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [4, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 60], [0, 1]]
 g := ![![[55, 46], [49], [46, 36], [45, 41], [24, 1]], ![[0, 15], [49], [56, 25], [53, 20], [48, 60]]]
 h' := ![![[24, 60], [49, 31], [60, 54], [3, 6], [26, 23], [0, 1]], ![[0, 1], [0, 30], [14, 7], [25, 55], [29, 38], [24, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44]]
 b := ![[], [41, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [4, 37, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-20922, 38428, 60422, 25966, 68036]
  a := ![-37, -20, -3, 10, 90]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-73236, -36060, 60422, 25966, 68036]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -8, -10, 2, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-1, -8, -10, 2, 0]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![51, 59, 1, 0, 0], ![41, 47, 0, 1, 0], ![37, 43, 0, 0, 1]] where
  M :=![![![-1, -8, -10, 2, 0], ![-28, -17, -10, -2, 68], ![164, 260, 189, -18, -340], ![-428, -1052, -742, 117, 748], ![44, 172, 118, -22, -53]]]
  hmulB := by decide  
  f := ![![![21635, 22952, 3834, -922, -8160]], ![![-3412, -3629, -606, 146, 1292]], ![![14797, 15689, 2621, -630, -5576]], ![![11911, 12629, 2110, -507, -4488]], ![![10851, 11505, 1922, -462, -4089]]]
  g := ![![![7, 8, -10, 2, 0], ![-32, -37, -10, -2, 68], ![63, 75, 189, -18, -340], ![81, 83, -742, 117, 748], ![-51, -57, 118, -22, -53]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P1 : CertificateIrreducibleZModOfList' 61 2 2 5 [51, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 60], [0, 1]]
 g := ![![[21, 16], [42], [18, 60], [40, 49], [27, 1]], ![[26, 45], [42], [52, 1], [21, 12], [54, 60]]]
 h' := ![![[27, 60], [2, 4], [58, 46], [34, 50], [26, 7], [0, 1]], ![[0, 1], [49, 57], [19, 15], [42, 11], [32, 54], [27, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [37, 56]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N1 : CertifiedPrimeIdeal' SI61N1 61 where
  n := 2
  hpos := by decide
  P := [51, 34, 1]
  hirr := P61P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2034, -396, 1242, 1527, 5325]
  a := ![-1, 0, 0, 3, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5328, -6138, 1242, 1527, 5325]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N1 B_one_repr
lemma NI61N1 : Nat.card (O ⧸ I61N1) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5001217, -16344499, -2919158, 579487, 6651900]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![-5001217, -16344499, -2919158, 579487, 6651900]] 
 ![![61, 0, 0, 0, 0], ![47, 1, 0, 0, 0], ![48, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![59, 0, 0, 0, 1]] where
  M :=![![![-5001217, -16344499, -2919158, 579487, 6651900], ![5190982, 16970487, 3031714, -601210, -6905042], ![-5393144, -17619506, -3143429, 626874, 7179028], ![5581820, 18307976, 3290704, -635933, -7402396], ![-1826804, -5966200, -1064236, 212374, 2431257]]]
  hmulB := by decide  
  f := ![![![6892253, 6646513, 5293804, -94735, -15900318]], ![![4810845, 4203852, 3407362, 7579, -11261224]], ![![6275092, 8045254, 6137335, -423730, -13731656]], ![![2561709, -1125607, -408612, 573428, -7253210]], ![![5684135, 5599763, 4444040, -98151, -13069017]]]
  g := ![![![8365053, -16344499, -2919158, 579487, 6651900], ![-8687631, 16970487, 3031714, -601210, -6905042], ![9006864, -17619506, -3143429, 626874, 7179028], ![-9433927, 18307976, 3290704, -635933, -7402396], ![3049367, -5966200, -1064236, 212374, 2431257]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-421, -1329, -868, 151, 622]] ![![-1, -8, -10, 2, 0]]
  ![![-141979, -251587, -185198, 21423, 284730]] where
 M := ![![![-141979, -251587, -185198, 21423, 284730]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![-141979, -251587, -185198, 21423, 284730]] ![![-5001217, -16344499, -2919158, 579487, 6651900]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![2317109461, 7574626688, 1352903018, -268519194, -3082659888]]]
 hmul := by decide  
 g := ![![![![37985401, 124174208, 22178738, -4401954, -50535408]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1, I61N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
    exact isPrimeI61N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0 ⊙ MulI61N1)


lemma PB2201I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB2201I1 : PrimesBelowBoundCertificateInterval O 23 61 2201 where
  m := 9
  g := ![1, 2, 1, 1, 2, 2, 3, 4, 3]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB2201I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0]
    · exact ![I31N0, I31N1]
    · exact ![I37N0]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0, I59N1, I59N2, I59N3]
    · exact ![I61N0, I61N1, I61N2]
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
    · exact ![20511149]
    · exact ![923521, 31]
    · exact ![69343957]
    · exact ![115856201]
    · exact ![3418801, 43]
    · exact ![4879681, 47]
    · exact ![2809, 2809, 53]
    · exact ![3481, 59, 59, 59]
    · exact ![3721, 3721, 61]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
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
      exact NI59N2
      exact NI59N3
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
      exact NI61N2
  β := ![I31N1, I43N1, I47N1, I53N2, I59N1, I59N2, I59N3, I61N2]
  Il := ![[], [I31N1], [], [], [I43N1], [I47N1], [I53N2], [I59N1, I59N2, I59N3], [I61N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
