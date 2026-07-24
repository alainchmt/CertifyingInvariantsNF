
import IdealArithmetic.Examples.NF5_1_632812500_4.RI5_1_632812500_4
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2915, -2052, 246, -532, 284]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![2915, -2052, 246, -532, 284]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![18, 10, 17, 1, 0], ![11, 16, 8, 0, 1]] where
  M :=![![![2915, -2052, 246, -532, 284], ![1916, 2135, -1272, 1974, -3404], ![-14160, 2460, 1591, -2070, 5580], ![4176, -2544, 204, -515, 36], ![-1582, -988, 660, -1030, 1829]]]
  hmulB := by decide  
  f := ![![![-617, 44, -102, 248, 484]], ![![956, 363, -936, -2706, 3436]], ![![15720, -1020, 2339, -6870, -11340]], ![![9022, -510, 1151, -4349, -5776]], ![![4355, -80, 134, -2994, -1175]]]
  g := ![![![323, -44, 242, -532, 284], ![132, 1271, -262, 1974, -3404], ![-1320, -2280, -271, -2070, 5580], ![450, 70, 299, -515, 36], ![-109, -688, 122, -1030, 1829]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [8, 12, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [15, 0, 26], [17, 28, 3], [0, 1]]
 g := ![![[9, 20, 1], [24, 24], [27, 13, 9], [1]], ![[25, 3, 4, 3], [1, 9], [26, 26, 6, 10], [7, 22, 6, 2]], ![[5, 4, 8, 15], [1, 13], [26, 23, 17, 2], [8, 16, 25, 27]]]
 h' := ![![[15, 0, 26], [6, 23, 1], [16, 13, 16], [21, 17, 3], [0, 1]], ![[17, 28, 3], [12, 10, 17], [7, 15, 3], [13, 1, 4], [15, 0, 26]], ![[0, 1], [25, 25, 11], [27, 1, 10], [6, 11, 22], [17, 28, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 6], []]
 b := ![[], [18, 22, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [8, 12, 26, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![548675, -135570, 335084, 298137, -1364328]
  a := ![5, -6, 4, 7, -20]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![351373, 645252, 213151, 298137, -1364328]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 24389 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-785, -7, -27, 510, 276]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![-785, -7, -27, 510, 276]] 
 ![![29, 0, 0, 0, 0], ![15, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![22, 0, 0, 0, 1]] where
  M :=![![![-785, -7, -27, 510, 276], ![-192, 511, -1303, -2493, 4908], ![19710, -270, 589, -13760, -5220], ![2372, -2606, 6494, 11977, -25148], ![-6756, -1027, 2725, 10800, -9347]]]
  hmulB := by decide  
  f := ![![![548359044859, 427344286737, 130659129898, -45275411797, 289429576708]], ![![316697421607, 246806968932, 75460430417, -26148207662, 167156175392]], ![![190175976267, 148206941591, 45313791793, -15701930551, 100376847664]], ![![171489535428, 133644322798, 40861318320, -14159079545, 90513950876]], ![![438912100382, 342050669605, 104580883046, -36238895435, 231662347173]]]
  g := ![![![-367, -7, -27, 510, 276], ![-2992, 511, -1303, -2493, 4908], ![8433, -270, 589, -13760, -5220], ![15636, -2606, 6494, 11977, -25148], ![3752, -1027, 2725, 10800, -9347]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-917553, -759892, 478763, -744217, 1302278]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![-917553, -759892, 478763, -744217, 1302278]] 
 ![![29, 0, 0, 0, 0], ![16, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![13, 0, 0, 1, 0], ![23, 0, 0, 0, 1]] where
  M :=![![![-917553, -759892, 478763, -744217, 1302278], ![5395268, -1103709, -573736, 719632, -2046902], ![-7579970, 4787630, -496071, 1113130, -383650], ![-675442, -1147472, 589004, -933759, 1550818], ![-2911492, 728542, 256137, -301109, 970737]]]
  hmulB := by decide  
  f := ![![![2254363, 246630, -661091, -3099961, 2186862]], ![![1683804, 75427, -217854, -1729846, 577610]], ![![-1459075, -185440, 493354, 2145325, -1665940]], ![![-1287135, 404330, -1005267, -1164392, 4042208]], ![![1465689, 417898, -1083070, -3401764, 3921411]]]
  g := ![![![-394161, -759892, 478763, -744217, 1302278], ![2194718, -1103709, -573736, 719632, -2046902], ![-3012015, 4787630, -496071, 1113130, -383650], ![-303133, -1147472, 589004, -933759, 1550818], ![-1181427, 728542, 256137, -301109, 970737]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![2915, -2052, 246, -532, 284]] ![![-785, -7, -27, 510, 276]]
  ![![-226239, -40673, 59037, -87238, 173392]] where
 M := ![![![-226239, -40673, 59037, -87238, 173392]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![-226239, -40673, 59037, -87238, 173392]] ![![-917553, -759892, 478763, -744217, 1302278]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![-905259362755, 725882191455, -121237265904, 234066549251, -200994203226]]]
 hmul := by decide  
 g := ![![![![-31215840095, 25030420395, -4180595376, 8071260319, -6930834594]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1, I29N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
    exact isPrimeI29N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0 ⊙ MulI29N1)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4615527, 1784427, -4598826, -13233819, 16895156]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![4615527, 1784427, -4598826, -13233819, 16895156]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![13, 27, 1, 0, 0], ![29, 18, 0, 1, 0], ![4, 7, 0, 0, 1]] where
  M :=![![![4615527, 1784427, -4598826, -13233819, 16895156], ![77153106, -4956955, 11356909, -33978141, -55185084], ![-97598970, -45988260, 118184411, 324274220, -437380380], ![-392137916, 22713818, -51431264, 186048107, 256410524], ![-139943936, 28252065, -69453670, -42043851, 287030965]]]
  hmulB := by decide  
  f := ![![![35235400197, 27459462565, 8395642075, -2909220088, 18597606476]], ![![61611259604, 48014566497, 14680296265, -5086948789, 32519058724]], ![![71912751149, 56042668694, 17134862951, -5937494417, 37956292116]], ![![69951747403, 54514425931, 16667608365, -5775583801, 36921252864]], ![![19836190732, 15458636080, 4726427546, -1637780099, 10469746089]]]
  g := ![![![12277432, 7932109, -4598826, -13233819, 16895156], ![36632894, 22138988, 11356909, -33978141, -55185084], ![-299626683, -193943247, 118184411, 324274220, -437380380], ![-198211893, -120399408, -51431264, 186048107, 256410524], ![26906503, 21002378, -69453670, -42043851, 287030965]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [22, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14, 30], [0, 1]]
 g := ![![[5, 16], [6, 19], [15, 20], [14, 1]], ![[12, 15], [24, 12], [16, 11], [28, 30]]]
 h' := ![![[14, 30], [23, 4], [11, 22], [2, 19], [0, 1]], ![[0, 1], [17, 27], [9, 9], [20, 12], [14, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [3, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [22, 17, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3248, -1220, 3909, 1823, -228]
  a := ![-1, -60, 0, -2, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3420, -4451, 3909, 1823, -228]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3258902795, -2539711180, -776508535, 269072307, -1720082964]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-3258902795, -2539711180, -776508535, 269072307, -1720082964]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![2, 5, 1, 0, 0], ![29, 14, 0, 1, 0], ![27, 21, 0, 0, 1]] where
  M :=![![![-3258902795, -2539711180, -776508535, 269072307, -1720082964], ![-5698393506, -4440841145, -1357772830, 470489296, -3007670436], ![-9963989900, -7765085350, -2374149301, 822679270, -5259096940], ![-3484529872, -2715545660, -830269390, 287701301, -1839171332], ![-3949438074, -3077855794, -941044389, 326086451, -2084554565]]]
  hmulB := by decide  
  f := ![![![1756859, 286530, -754455, -2923583, 2619740]], ![![13706386, -1470567, 3513956, -2860746, -15529444]], ![![1005768, -462075, 1156169, 1696434, -4576840]], ![![5550245, -169376, 342129, -3452052, -2152896]], ![![10292895, -548771, 1229686, -5138690, -6270029]]]
  g := ![![![1191395400, 1087018111, -776508535, 269072307, -1720082964], ![2083227882, 1900717807, -1357772830, 470489296, -3007670436], ![3642652492, 3323522165, -2374149301, 822679270, -5259096940], ![1273880553, 1162276808, -830269390, 287701301, -1839171332], ![1443842480, 1317348442, -941044389, 326086451, -2084554565]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P1 : CertificateIrreducibleZModOfList' 31 2 2 4 [15, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 30], [0, 1]]
 g := ![![[24, 1], [12, 14], [19, 25], [12, 1]], ![[5, 30], [25, 17], [9, 6], [24, 30]]]
 h' := ![![[12, 30], [6, 1], [25, 13], [6, 5], [0, 1]], ![[0, 1], [18, 30], [26, 18], [4, 26], [12, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [9, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N1 : CertifiedPrimeIdeal' SI31N1 31 where
  n := 2
  hpos := by decide
  P := [15, 19, 1]
  hirr := P31P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1717, 1051, -1092, -4469, 6010]
  a := ![-5, 25, -4, -8, 21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-928, -1843, -1092, -4469, 6010]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N1 B_one_repr
lemma NI31N1 : Nat.card (O ⧸ I31N1) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 5, 0, 1, 0]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![1, 5, 0, 1, 0]] 
 ![![31, 0, 0, 0, 0], ![30, 1, 0, 0, 0], ![30, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![26, 0, 0, 0, 1]] where
  M :=![![![1, 5, 0, 1, 0], ![-2, 3, 3, -3, 8], ![30, 0, 1, 0, 0], ![0, 6, 0, 1, 0], ![8, 3, 0, 1, -1]]]
  hmulB := by decide  
  f := ![![![3, -1, 3, 2, -8]], ![![2, -1, 3, 3, -8]], ![![0, 0, 1, 0, 0]], ![![6, 0, 0, -5, 0]], ![![6, -1, 3, 0, -9]]]
  g := ![![![-5, 5, 0, 1, 0], ![-12, 3, 3, -3, 8], ![0, 0, 1, 0, 0], ![-6, 6, 0, 1, 0], ![-2, 3, 0, 1, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![4615527, 1784427, -4598826, -13233819, 16895156]] ![![-3258902795, -2539711180, -776508535, 269072307, -1720082964]]
  ![![-3, 1, -3, -2, 8]] where
 M := ![![![-3, 1, -3, -2, 8]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![-3, 1, -3, -2, 8]] ![![1, 5, 0, 1, 0]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![-31, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1, I31N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
    exact isPrimeI31N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0 ⊙ MulI31N1)
instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5415, 2313, 1128, -617, 2396]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![5415, 2313, 1128, -617, 2396]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![22, 8, 1, 0, 0], ![24, 36, 0, 1, 0], ![17, 29, 0, 0, 1]] where
  M :=![![![5415, 2313, 1128, -617, 2396], ![8422, 6577, 1151, 303, 2252], ![6150, 11280, 3719, -1910, 9180], ![6272, 2302, 1184, -643, 2452], ![4218, 3547, 1510, -887, 3527]]]
  hmulB := by decide  
  f := ![![![16155, -827, 1843, -8250, -9508]], ![![-12024, -9853, 25181, 62489, -94524]], ![![-4036, -2124, 5451, 14606, -20244]], ![![-112, -8762, 22226, 47251, -85028]], ![![2809, -7679, 19433, 39125, -74785]]]
  g := ![![![-1225, -1459, 1128, -617, 2396], ![-1688, -2131, 1151, 303, 2252], ![-5024, -5836, 3719, -1910, 9180], ![-1244, -1490, 1184, -643, 2452], ![-1829, -2132, 1510, -887, 3527]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [34, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 36], [0, 1]]
 g := ![![[12, 12], [26], [5, 12], [1], [1]], ![[0, 25], [26], [30, 25], [1], [1]]]
 h' := ![![[36, 36], [7, 7], [15, 27], [12, 30], [3, 36], [0, 1]], ![[0, 1], [0, 30], [25, 10], [19, 7], [4, 1], [36, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [17, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [34, 1, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3538, 1823, -4589, -7156, 18236]
  a := ![8, -9, 9, 13, -33]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1104, -6289, -4589, -7156, 18236]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![283597, 325536, 79828, -18014, 183630]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![283597, 325536, 79828, -18014, 183630]] 
 ![![37, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![12, 0, 0, 0, 1]] where
  M :=![![![283597, 325536, 79828, -18014, 183630], ![586918, 431199, 177934, -97708, 406778], ![1415750, 798280, 219837, -37540, 438670], ![278218, 355868, 86938, -20841, 203138], ![463826, 361564, 87336, -11302, 185393]]]
  hmulB := by decide  
  f := ![![![28564929, 3906448, -10358672, -43485586, 35293558]], ![![19108664, 1275767, -3537082, -21890752, 10629190]], ![![-11202517, -1849424, 4867509, 18762538, -16921844]], ![![-17775802, 4271500, -10554190, -9016257, 43086682]], ![![4069782, 3723108, -9507556, -23240010, 35760769]]]
  g := ![![![-223835, 325536, 79828, -18014, 183630], ![-337430, 431199, 177934, -97708, 406778], ![-533659, 798280, 219837, -37540, 438670], ![-245876, 355868, 86938, -20841, 203138], ![-241066, 361564, 87336, -11302, 185393]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![869096092381, -43356417699, -146499394095, 204140697556, -465092417832]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![869096092381, -43356417699, -146499394095, 204140697556, -465092417832]] 
 ![![37, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![34, 0, 1, 0, 0], ![28, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![869096092381, -43356417699, -146499394095, 204140697556, -465092417832], ![-1803558648608, 812285069661, 13454605021, 50358190353, 237848326952], ![612828600150, -1464993940950, 473720362003, -797346526810, 1116410503680], ![988784912932, 26909210042, -197342278202, 282281975881, -605908140688], ![894379130906, -451637812811, 12969911267, -57014376020, -68781689911]]]
  hmulB := by decide  
  f := ![![![-6700600755603, 1239130732981, -3037357187704, -1401639633905, 12640735868848]], ![![-2883452155376, 821560323541, -2038383351285, -2155139097007, 8237980531080]], ![![-1348243372916, 317753325522, -784708913111, -650335799160, 3207559297296]], ![![-10370739072296, 472946183442, -1036134586932, 5608032604911, 5541262858848]], ![![-4463228314145, 142744344156, -291712945194, 2740760615752, 1794730352305]]]
  g := ![![![41974853169, -43356417699, -146499394095, 204140697556, -465092417832], ![-588626065100, 812285069661, 13454605021, 50358190353, 237848326952], ![1025553925404, -1464993940950, 473720362003, -797346526810, 1116410503680], ![-5177498192, 26909210042, -197342278202, 282281975881, -605908140688], ![325800493193, -451637812811, 12969911267, -57014376020, -68781689911]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2

def I37N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23, -15, 39, 100, -146]] i)))

def SI37N3: IdealEqSpanCertificate' Table ![![-23, -15, 39, 100, -146]] 
 ![![37, 0, 0, 0, 0], ![26, 1, 0, 0, 0], ![27, 0, 1, 0, 0], ![15, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![-23, -15, 39, 100, -146], ![-638, 31, -69, 333, 362], ![420, 390, -997, -2430, 3750], ![3222, -138, 300, -1789, -1638], ![1300, -215, 525, 136, -2207]]]
  hmulB := by decide  
  f := ![![![-1012331, -788911, -241200, 83573, -534290]], ![![-759206, -591653, -180891, 62677, -400698]], ![![-822381, -640881, -195943, 67893, -434040]], ![![-439659, -342627, -104754, 36296, -232044]], ![![-498283, -388312, -118722, 41136, -262985]]]
  g := ![![![8, -15, 39, 100, -146], ![-290, 31, -69, 333, 362], ![-273, 390, -997, -2430, 3750], ![1443, -138, 300, -1789, -1638], ![762, -215, 525, 136, -2207]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N3 : Nat.card (O ⧸ I37N3) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N3)

lemma isPrimeI37N3 : Ideal.IsPrime I37N3 := prime_ideal_of_norm_prime hp37.out _ NI37N3
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![5415, 2313, 1128, -617, 2396]] ![![283597, 325536, 79828, -18014, 183630]]
  ![![5429851679, 4307337355, 1247422408, -380110229, 2748919206]] where
 M := ![![![5429851679, 4307337355, 1247422408, -380110229, 2748919206]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![5429851679, 4307337355, 1247422408, -380110229, 2748919206]] ![![869096092381, -43356417699, -146499394095, 204140697556, -465092417832]]
  ![![-202287823858099033733, 184156312712738744750, -35922006766364590566, 66709319576405347490, -67017809841257819642]] where
 M := ![![![-202287823858099033733, 184156312712738744750, -35922006766364590566, 66709319576405347490, -67017809841257819642]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N2 : IdealMulLeCertificate' Table 
  ![![-202287823858099033733, 184156312712738744750, -35922006766364590566, 66709319576405347490, -67017809841257819642]] ![![-23, -15, 39, 100, -146]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![-112075522321305334181, -63476572589310458085, 46675744681910025915, -71648670802176427092, 129522964930718663292]]]
 hmul := by decide  
 g := ![![![![-3029068170846090113, -1715583042954336705, 1261506613024595295, -1936450562220984516, 3500620673803207116]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N2, I37N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N2
    exact isPrimeI37N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1 ⊙ MulI37N2)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![453619, -162500, -16329, 10261, -91992]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![453619, -162500, -16329, 10261, -91992]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![21, 18, 19, 1, 0], ![35, 6, 9, 0, 1]] where
  M :=![![![453619, -162500, -16329, 10261, -91992], ![-296498, 382149, -91030, 163548, -193888], ![-908760, -163290, 248941, -364130, 726720], ![581684, -182060, -32350, 31387, -146576], ![115658, -183022, 56497, -94607, 128609]]]
  hmulB := by decide  
  f := ![![![-227477, 84746, -211367, -277311, 843352]], ![![3084678, 61253, -203984, -2754958, 311568]], ![![6444620, -2113670, 5259601, 6310250, -21104960]], ![![3853851, -919158, 2270638, 1917522, -9274200]], ![![1442423, -367074, 908323, 841766, -3694871]]]
  g := ![![![84338, 4994, 15040, 10261, -91992], ![74514, -34107, -35450, 163548, -193888], ![-456030, 49530, 15291, -364130, 726720], ![123237, 3230, 16841, 31387, -146576], ![-58510, 18250, 16989, -94607, 128609]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [17, 36, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 33, 1], [29, 7, 40], [0, 1]]
 g := ![![[40, 22, 8], [21, 33], [15, 36], [30, 5, 1], []], ![[12, 14, 5, 25], [29, 2], [33, 37], [20, 22, 39, 8], [30, 1]], ![[8, 35, 10, 37], [6, 25], [22, 2], [4, 10, 15, 18], [32, 1]]]
 h' := ![![[17, 33, 1], [17, 13, 34], [28, 34, 22], [23, 24, 35], [0, 0, 1], [0, 1]], ![[29, 7, 40], [22, 8, 5], [8, 32, 24], [35, 27, 23], [25, 25, 7], [17, 33, 1]], ![[0, 1], [37, 20, 2], [4, 16, 36], [3, 31, 24], [10, 16, 33], [29, 7, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 14], []]
 b := ![[], [22, 19, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [17, 36, 36, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3949393, -259136, 599768, -1700296, -2897504]
  a := ![6, -6, 8, 4, -24]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3440689, 1164176, 1438608, -1700296, -2897504]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1209, 942, 288, -100, 638]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![1209, 942, 288, -100, 638]] 
 ![![41, 0, 0, 0, 0], ![30, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![29, 0, 0, 1, 0], ![23, 0, 0, 0, 1]] where
  M :=![![![1209, 942, 288, -100, 638], ![2114, 1647, 504, -174, 1114], ![3690, 2880, 881, -300, 1950], ![1290, 1008, 306, -109, 690], ![1466, 1142, 348, -124, 777]]]
  hmulB := by decide  
  f := ![![![1537, -542, -72, 56, -354]], ![![1096, -365, -60, 54, -274]], ![![4, -44, 17, -28, 42]], ![![1135, -398, -54, 43, -264]], ![![873, -320, -36, 24, -189]]]
  g := ![![![-961, 942, 288, -100, 638], ![-1680, 1647, 504, -174, 1114], ![-2942, 2880, 881, -300, 1950], ![-1031, 1008, 306, -109, 690], ![-1165, 1142, 348, -124, 777]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-130941, 1396, -1477, 95435, 25558]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![-130941, 1396, -1477, 95435, 25558]] 
 ![![41, 0, 0, 0, 0], ![39, 1, 0, 0, 0], ![37, 0, 1, 0, 0], ![23, 0, 0, 1, 0], ![29, 0, 0, 0, 1]] where
  M :=![![![-130941, 1396, -1477, 95435, 25558], ![-114196, 85487, -215032, -370364, 840154], ![3261190, -14770, -13939, -2484530, -442450], ![728342, -430064, 1079348, 1742249, -4240718], ![-941592, -189474, 495429, 1760179, -1752551]]]
  hmulB := by decide  
  f := ![![![23022779, 17932302, 5483073, -1899641, 12144678]], ![![22881017, 17822633, 5449433, -1887945, 12070228]], ![![22492513, 17520144, 5357182, -1856187, 11865996]], ![![13515667, 10527238, 3218855, -1115182, 7129564]], ![![16964739, 13213862, 4040380, -1399854, 8949231]]]
  g := ![![![-74803, 1396, -1477, 95435, 25558], ![-276539, 85487, -215032, -370364, 840154], ![1812883, -14770, -13939, -2484530, -442450], ![1474977, -430064, 1079348, 1742249, -4240718], ![-37637, -189474, 495429, 1760179, -1752551]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![453619, -162500, -16329, 10261, -91992]] ![![1209, 942, 288, -100, 638]]
  ![![23022779, 17932302, 5483073, -1899641, 12144678]] where
 M := ![![![23022779, 17932302, 5483073, -1899641, 12144678]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![23022779, 17932302, 5483073, -1899641, 12144678]] ![![-130941, 1396, -1477, 95435, 25558]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![41, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1, I41N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
    exact isPrimeI41N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0 ⊙ MulI41N1)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![52305135, -3127727, 7108845, -24288144, -35152856]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![52305135, -3127727, 7108845, -24288144, -35152856]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![9, 3, 18, 2, 1]] where
  M :=![![![52305135, -3127727, 7108845, -24288144, -35152856], ![-56882280, -31424009, 80601417, 213867225, -299763720], ![-1327025610, 71088450, -159394739, 660696570, 811646640], ![222709356, 161202834, -412390266, -1042800665, 1544102496], ![618795062, 45448561, -125030469, -731147052, 384340583]]]
  hmulB := by decide  
  f := ![![![468875668421, 365401719791, 111720390942, -38712845493, 247477428368]], ![![819857976090, 638927405803, 195349982409, -67691793915, 432729521160]], ![![1433572151310, 1117203909420, 341581472473, -118363269690, 756654212160]], ![![501337835172, 390699964818, 119455247328, -41393093009, 264611295792]], ![![791968744099, 617192916407, 188704732785, -65389112053, 418009296231]]]
  g := ![![![8573973, 2379787, 14880471, 1070176, -35152856], ![61418400, 20182957, 127356939, 18916155, -299763720], ![-200740590, -54973290, -343465913, -22385970, 811646640], ![-318004956, -103979178, -655958958, -96069899, 1544102496], ![-66052795, -25757516, -163794441, -34879726, 384340583]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 4 2 5 [39, 42, 33, 19, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 38, 30, 27], [12, 42], [8, 5, 13, 16], [0, 1]]
 g := ![![[1, 28, 23, 31], [16, 40, 13, 36], [11, 23, 41], [24, 1], []], ![[15, 32, 38, 38, 35, 28], [27, 34, 12, 29, 42, 8], [5, 10, 23], [32, 26, 8, 41, 10, 7], [25, 24, 41]], ![[27, 3, 21, 12], [33, 6, 19, 7], [42, 25, 41], [36, 42], []], ![[38, 29, 2, 16, 38, 15], [34, 26, 15, 23, 6, 35], [40, 40, 23], [12, 19, 20, 20, 0, 36], [25, 24, 41]]]
 h' := ![![[4, 38, 30, 27], [21, 14, 18, 17], [15, 18, 10, 37], [10, 28, 26, 27], [0, 0, 1], [0, 1]], ![[12, 42], [17, 20, 9, 3], [17, 14, 40, 8], [30, 26, 27, 25], [30, 38, 15, 23], [4, 38, 30, 27]], ![[8, 5, 13, 16], [36, 36, 28, 26], [32, 12, 9, 6], [6, 25, 9, 16], [15, 19, 1], [12, 42]], ![[0, 1], [29, 16, 31, 40], [32, 42, 27, 35], [1, 7, 24, 18], [35, 29, 26, 20], [8, 5, 13, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [42], []]
 b := ![[], [], [32, 16, 9, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 4
  hpos := by decide
  P := [39, 42, 33, 19, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![408974284, 63503430, -166247816, -660573942, 574858471]
  a := ![7, 5, 8, 11, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-110808185, -38629581, -244504658, -42099788, 574858471]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 3418801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17967, 20804, -4978, 8854, -10444]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-17967, 20804, -4978, 8854, -10444]] 
 ![![43, 0, 0, 0, 0], ![24, 1, 0, 0, 0], ![26, 0, 1, 0, 0], ![30, 0, 0, 1, 0], ![29, 0, 0, 0, 1]] where
  M :=![![![-17967, 20804, -4978, 8854, -10444], ![-49040, -10703, 13540, -20120, 39500], ![158740, -49780, -9963, 9560, -42460], ![-29300, 27080, -5288, 9777, -10180], ![30204, 3096, -6890, 10146, -20959]]]
  hmulB := by decide  
  f := ![![![-47032113969013, -36652819692228, -11206480764874, 3883219120022, -24824036304972]], ![![-28163006567704, -21947846154591, -6710482790332, 2325286200256, -14864726215676]], ![![-31782188988826, -24768328363876, -7572836079695, 2624104968764, -16774968138364]], ![![-33982599006910, -26483140326080, -8097134276428, 2805782412813, -17936367309380]], ![![-33044863870735, -25752349511788, -7873697354732, 2728358059472, -17441421003539]]]
  g := ![![![-8153, 20804, -4978, 8854, -10444], ![-15956, -10703, 13540, -20120, 39500], ![59466, -49780, -9963, 9560, -42460], ![-12554, 27080, -5288, 9777, -10180], ![10197, 3096, -6890, 10146, -20959]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![52305135, -3127727, 7108845, -24288144, -35152856]] ![![-17967, 20804, -4978, 8854, -10444]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![-8038816589, 1197604825, -2910925033, -125970134, 12360409684]]]
 hmul := by decide  
 g := ![![![![-186949223, 27851275, -67695931, -2929538, 287451388]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![479, -4386, 1674, -2750, 4136]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![479, -4386, 1674, -2750, 4136]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![29, 30, 36, 1, 0], ![22, 4, 6, 0, 1]] where
  M :=![![![479, -4386, 1674, -2750, 4136], ![17908, -885, -3022, 4212, -9592], ![-37200, 16740, 283, 1030, 4920], ![2540, -6044, 1952, -3287, 4600], ![-10158, 1114, 1468, -1988, 4825]]]
  hmulB := by decide  
  f := ![![![10865, 8470, 2590, -894, 5736]], ![![18996, 14813, 4522, -1576, 10056]], ![![33320, 25900, 7909, -2830, 17560]], ![![44599, 34712, 10602, -3745, 23536]], ![![11236, 8750, 2674, -936, 5929]]]
  g := ![![![-229, 1310, 1614, -2750, 4136], ![2272, -1891, -2066, 4212, -9592], ![-3730, -720, -1411, 1030, 4920], ![-71, 1578, 1972, -3287, 4600], ![-1248, 882, 938, -1988, 4825]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [44, 42, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 40, 19], [0, 6, 28], [0, 1]]
 g := ![![[46, 28, 32], [36, 22, 7], [36, 33, 2], [14, 44, 1], []], ![[14, 15, 34, 10], [44, 7, 42, 30], [6, 44, 43, 43], [38, 39, 0, 26], [14, 32]], ![[0, 9, 40, 9], [35, 19, 36, 14], [27, 16, 18, 1], [26, 20, 23, 9], [5, 32]]]
 h' := ![![[44, 40, 19], [14, 19, 28], [14, 22, 17], [42, 14, 40], [0, 0, 1], [0, 1]], ![[0, 6, 28], [22, 4, 12], [16, 45, 3], [19, 44, 36], [4, 20, 6], [44, 40, 19]], ![[0, 1], [11, 24, 7], [34, 27, 27], [31, 36, 18], [15, 27, 40], [0, 6, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 8], []]
 b := ![[], [31, 19, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [44, 42, 3, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-464, 210, -465, -775, 1776]
  a := ![-1, -3, 0, -2, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-363, 348, 357, -775, 1776]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10865, 8470, 2590, -894, 5736]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![10865, 8470, 2590, -894, 5736]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![33, 8, 1, 0, 0], ![13, 22, 0, 1, 0], ![22, 43, 0, 0, 1]] where
  M :=![![![10865, 8470, 2590, -894, 5736], ![18996, 14813, 4522, -1576, 10056], ![33320, 25900, 7909, -2830, 17560], ![11668, 9044, 2800, -929, 6008], ![13158, 10258, 3156, -1040, 6887]]]
  hmulB := by decide  
  f := ![![![479, -4386, 1674, -2750, 4136]], ![![17908, -885, -3022, 4212, -9592]], ![![2593, -2874, 667, -1192, 1376]], ![![8569, -1756, -910, 1141, -3248]], ![![16392, -2839, -1950, 2524, -6737]]]
  g := ![![![-4025, -5090, 2590, -894, 5736], ![-7042, -8917, 4522, -1576, 10056], ![-12281, -15536, 7909, -2830, 17560], ![-4273, -5346, 2800, -929, 6008], ![-4872, -6133, 3156, -1040, 6887]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P1 : CertificateIrreducibleZModOfList' 47 2 2 5 [18, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 46], [0, 1]]
 g := ![![[27, 34], [39, 32], [24, 2], [5, 21], [1]], ![[0, 13], [44, 15], [39, 45], [45, 26], [1]]]
 h' := ![![[31, 46], [3, 9], [38, 19], [4, 7], [29, 31], [0, 1]], ![[0, 1], [0, 38], [16, 28], [33, 40], [3, 16], [31, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [4, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N1 : CertifiedPrimeIdeal' SI47N1 47 where
  n := 2
  hpos := by decide
  P := [18, 16, 1]
  hirr := P47P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3470, 1340, -2290, -2556, 9791]
  a := ![4, -1, 11, 4, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2342, -7343, -2290, -2556, 9791]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N1 B_one_repr
lemma NI47N1 : Nat.card (O ⧸ I47N1) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![479, -4386, 1674, -2750, 4136]] ![![10865, 8470, 2590, -894, 5736]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![47, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-101747, -79467, -24286, 8275, -53886]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-101747, -79467, -24286, 8275, -53886]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![15, 34, 31, 4, 1]] where
  M :=![![![-101747, -79467, -24286, 8275, -53886], ![-178208, -139083, -42131, 15403, -95458], ![-317180, -242860, -74431, 29510, -163150], ![-109694, -84262, -27746, 5753, -50674], ![-121756, -96017, -30188, 7257, -62647]]]
  hmulB := by decide  
  f := ![![![11625, 9233, -5907, 9170, -16102]], ![![-66646, 13863, 6995, -8739, 25054]], ![![92640, -59070, 6287, -13970, 5250]], ![![8738, 13990, -7276, 11519, -19202]], ![![16059, -22160, 5885, -10244, 12913]]]
  g := ![![![13331, 33069, 31060, 4223, -53886], ![23654, 58613, 55039, 7495, -95458], ![40190, 100080, 94023, 12870, -163150], ![12272, 30918, 29116, 3933, -50674], ![15433, 38377, 36073, 4865, -62647]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 4 2 5 [22, 30, 41, 9, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 28, 28, 6], [48, 26, 27, 51], [29, 51, 51, 49], [0, 1]]
 g := ![![[28, 50, 24, 4], [17, 36, 40], [7, 38, 11, 17], [40, 44, 1], []], ![[21, 40, 27, 3, 36, 15], [12, 52, 44], [17, 42, 15, 40, 38, 49], [30, 37, 24], [8, 43, 14, 44, 20, 4]], ![[29, 23, 35, 20, 11, 22], [46, 0, 46], [42, 29, 15, 42, 41, 32], [42, 21, 28], [25, 39, 41, 16, 25, 45]], ![[32, 26, 26, 27, 41, 24], [23, 20, 37], [0, 6, 39, 8, 36, 11], [9, 44, 40], [28, 12, 35, 15, 3, 42]]]
 h' := ![![[20, 28, 28, 6], [22, 15, 38, 51], [5, 31, 25, 27], [21, 5, 39, 32], [0, 0, 0, 1], [0, 1]], ![[48, 26, 27, 51], [30, 46, 32, 20], [20, 52, 14, 16], [5, 14, 12, 21], [33, 31, 9, 17], [20, 28, 28, 6]], ![[29, 51, 51, 49], [11, 19, 49, 25], [4, 49, 2, 24], [14, 10, 29, 14], [14, 24, 24, 9], [48, 26, 27, 51]], ![[0, 1], [18, 26, 40, 10], [43, 27, 12, 39], [7, 24, 26, 39], [29, 51, 20, 26], [29, 51, 51, 49]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [18, 43, 29], []]
 b := ![[], [], [26, 35, 43, 41], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 4
  hpos := by decide
  P := [22, 30, 41, 9, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-270708069, 96414462, -240278570, -306115353, 960546661]
  a := ![-5, 7, -6, -8, 21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-276960528, -614380604, -566362737, -78269849, 960546661]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 7890481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11625, 9233, -5907, 9170, -16102]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![11625, 9233, -5907, 9170, -16102]] 
 ![![53, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![47, 0, 1, 0, 0], ![11, 0, 0, 1, 0], ![46, 0, 0, 0, 1]] where
  M :=![![![11625, 9233, -5907, 9170, -16102], ![-66646, 13863, 6995, -8739, 25054], ![92640, -59070, 6287, -13970, 5250], ![8738, 13990, -7276, 11519, -19202], ![35924, -9107, -3113, 3638, -11859]]]
  hmulB := by decide  
  f := ![![![-101747, -79467, -24286, 8275, -53886]], ![![-37918, -29613, -9043, 3101, -20102]], ![![-96213, -75053, -22941, 7895, -50864]], ![![-23187, -18083, -5564, 1826, -12140]], ![![-90606, -70783, -21648, 7319, -47951]]]
  g := ![![![14394, 9233, -5907, 9170, -16102], ![-32100, 13863, 6995, -8739, 25054], ![14577, -59070, 6287, -13970, 5250], ![16141, 13990, -7276, 11519, -19202], ![16069, -9107, -3113, 3638, -11859]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-101747, -79467, -24286, 8275, -53886]] ![![11625, 9233, -5907, 9170, -16102]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![53, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0, 0, 0]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]] where
  M :=![![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 5 2 5 [9, 58, 24, 40, 40, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [34, 41, 35, 35, 8], [58, 35, 41, 13, 16], [53, 47, 17, 36, 24], [51, 53, 25, 34, 11], [0, 1]]
 g := ![![[29, 43, 52, 2, 9], [42, 10, 46, 20, 9], [12, 19, 39, 25], [26, 19, 1], []], ![[52, 49, 34, 28, 52, 56, 1, 43], [47, 14, 25, 47, 46, 32, 0, 47], [10, 56, 5, 21], [21, 55, 41, 15, 8, 55, 35, 31], [39, 52, 24, 57, 20, 53, 46, 40]], ![[23, 52, 43, 36, 24, 37, 18, 9], [2, 38, 41, 9, 44, 25], [42, 28, 52, 3], [15, 14, 56, 26, 4, 42, 49, 35], [46, 34, 45, 34, 28, 23, 16, 25]], ![[50, 30, 20, 55, 49, 45, 4, 6], [34, 38, 22, 48, 23, 29, 43, 52], [55, 37, 46, 16], [1, 0, 26, 47, 52, 32, 13, 8], [3, 36, 21, 48, 55, 28, 10, 18]], ![[29, 14, 44, 30, 52, 3, 53, 38], [3, 38, 2, 47, 7, 7, 2, 30], [47, 28, 22, 35], [8, 36, 35, 50, 7, 42, 23, 52], [0, 14, 19, 35, 9, 28, 48, 33]]]
 h' := ![![[34, 41, 35, 35, 8], [35, 30, 21, 38, 56], [14, 28, 13, 35, 56], [2, 32, 35, 39, 5], [0, 0, 0, 1], [0, 1]], ![[58, 35, 41, 13, 16], [37, 51, 18, 28, 36], [31, 17, 15, 50, 38], [11, 42, 6, 8, 27], [13, 41, 46, 15, 47], [34, 41, 35, 35, 8]], ![[53, 47, 17, 36, 24], [25, 30, 29, 3, 45], [4, 9, 4, 43], [38, 58, 9, 19, 48], [57, 22, 47, 58, 38], [58, 35, 41, 13, 16]], ![[51, 53, 25, 34, 11], [51, 9, 30, 27, 30], [41, 11, 37, 36, 37], [51, 52, 9, 12, 4], [52, 35, 22, 26, 16], [53, 47, 17, 36, 24]], ![[0, 1], [14, 57, 20, 22, 10], [31, 53, 49, 13, 46], [49, 52, 0, 40, 34], [19, 20, 3, 18, 17], [51, 53, 25, 34, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55, 56, 58, 14], [], [], []]
 b := ![[], [41, 34, 44, 6, 13], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 5
  hpos := by decide
  P := [9, 58, 24, 40, 40, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2426006486, -23997483, 99460194, 2037405995, -11544648]
  a := ![-1, 5, -2, -1, 8]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-41118754, -406737, 1685766, 34532305, -195672]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 714924299 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def PBC59 : ContainsPrimesAboveP 59 ![I59N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![59, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 59 (by decide) 𝕀

instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-18277, 25638, -64741, -123631, 250502]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-18277, 25638, -64741, -123631, 250502]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![53, 4, 53, 1, 0], ![33, 36, 3, 0, 1]] where
  M :=![![![-18277, 25638, -64741, -123631, 250502], ![998768, -15037, 22398, -704318, -237542], ![696010, -647410, 1631141, 2937570, -6347170], ![-4983330, 44796, -35076, 3676901, 891810], ![-2533804, 272900, -652255, 523213, 2880977]]]
  hmulB := by decide  
  f := ![![![3725031, 2902836, 887357, -307331, 1965550]], ![![6511312, 5075919, 1551948, -537872, 3438002]], ![![11389750, 8873570, 2713661, -940650, 6011030]], ![![13624779, 10615690, 3246074, -1124968, 7190366]], ![![6492085, 5060080, 1547039, -536064, 3426993]]]
  g := ![![![-28400, -139310, 94036, -123631, 250502], ![756828, 186127, 623998, -704318, -237542], ![892810, 3542630, -2213419, 2937570, -6347170], ![-3758833, -766688, -3239119, 3676901, 891810], ![-2054694, -1730084, -606975, 523213, 2880977]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [53, 2, 44, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [31, 21, 43], [47, 39, 18], [0, 1]]
 g := ![![[42, 43, 13], [44, 46], [22, 51, 52], [18, 26, 45], [1]], ![[57, 19, 43, 40], [39, 15], [30, 19, 34, 40], [59, 21, 15, 40], [9, 5, 19, 24]], ![[2, 0, 44, 51], [16, 36], [8, 30], [58, 47, 18, 33], [50, 60, 46, 37]]]
 h' := ![![[31, 21, 43], [35, 59, 14], [54, 55, 31], [22, 53, 33], [8, 59, 17], [0, 1]], ![[47, 39, 18], [6, 47, 33], [50, 58, 36], [13, 20, 28], [34, 53, 28], [31, 21, 43]], ![[0, 1], [55, 16, 14], [7, 9, 55], [28, 49], [35, 10, 16], [47, 39, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8], []]
 b := ![[], [8, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [53, 2, 44, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12416063, 3762675, -8933536, -10357304, 36479355]
  a := ![-2, 11, -27, -3, 15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-10939306, -20787949, 7058451, -10357304, 36479355]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-326629, 30228, -71523, 94097, 323330]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-326629, 30228, -71523, 94097, 323330]] 
 ![![61, 0, 0, 0, 0], ![45, 1, 0, 0, 0], ![49, 0, 1, 0, 0], ![47, 0, 0, 1, 0], ![59, 0, 0, 0, 1]] where
  M :=![![![-326629, 30228, -71523, 94097, 323330], ![781796, 184895, -481296, -1609896, 1722766], ![8388090, -715230, 1681921, -2745090, -7710870], ![-3528486, -962592, 2497164, 7955497, -9018666], ![-4874140, -157966, 477495, 4682453, -1086079]]]
  hmulB := by decide  
  f := ![![![-4751017, 697894, 616299, -814499, 2080562]], ![![-3375821, 444357, 458685, -612609, 1530344]], ![![-3806383, 661636, 452572, -585341, 1563788]], ![![-3752681, 545798, 488985, -646920, 1648852]], ![![-4656983, 713158, 592410, -779304, 2010119]]]
  g := ![![![-355431, 30228, -71523, 94097, 323330], ![-162837, 184895, -481296, -1609896, 1722766], ![8887211, -715230, 1681921, -2745090, -7710870], ![1239673, -962592, 2497164, 7955497, -9018666], ![-2904255, -157966, 477495, 4682453, -1086079]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-975, 2, 11, 757, 106]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![-975, 2, 11, 757, 106]] 
 ![![61, 0, 0, 0, 0], ![56, 1, 0, 0, 0], ![36, 0, 1, 0, 0], ![36, 0, 0, 1, 0], ![46, 0, 0, 0, 1]] where
  M :=![![![-975, 2, 11, 757, 106], ![-1196, 645, -1618, -2534, 6374], ![24190, 110, -661, -19610, -1150], ![7154, -3236, 8096, 11795, -32066], ![-6188, -1512, 3933, 13005, -14109]]]
  hmulB := by decide  
  f := ![![![-85664427, -66759516, -20411499, 7072893, -45214526]], ![![-81098316, -63201083, -19323520, 6695892, -42804490]], ![![-54849762, -42745206, -13069205, 4528678, -28950246]], ![![-52057618, -40569248, -12403912, 4298143, -27476522]], ![![-66301306, -51669558, -15797795, 5474175, -34994481]]]
  g := ![![![-551, 2, 11, 757, 106], ![-2968, 645, -1618, -2534, 6374], ![13126, 110, -661, -19610, -1150], ![15530, -3236, 8096, 11795, -32066], ![1930, -1512, 3933, 13005, -14109]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-18277, 25638, -64741, -123631, 250502]] ![![-326629, 30228, -71523, 94097, 323330]]
  ![![-1301791416223, 129927978904, -309034918432, 324143338972, 1380389941556]] where
 M := ![![![-1301791416223, 129927978904, -309034918432, 324143338972, 1380389941556]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![-1301791416223, 129927978904, -309034918432, 324143338972, 1380389941556]] ![![-975, 2, 11, 757, 106]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![-12584633420164679, -3088871314012950, 8033067018095487, 26520723022938493, -28824340789278498]]]
 hmul := by decide  
 g := ![![![![-206305465904339, -50637234655950, 131689623247467, 434765951195713, -472530176873418]]]]
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


lemma PB1567I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB1567I1 : PrimesBelowBoundCertificateInterval O 23 61 1567 where
  m := 9
  g := ![3, 3, 4, 3, 2, 2, 2, 1, 3]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB1567I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1, I29N2]
    · exact ![I31N0, I31N1, I31N2]
    · exact ![I37N0, I37N1, I37N2, I37N3]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
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
    · exact ![24389, 29, 29]
    · exact ![961, 961, 31]
    · exact ![1369, 37, 37, 37]
    · exact ![68921, 41, 41]
    · exact ![3418801, 43]
    · exact ![103823, 2209]
    · exact ![7890481, 53]
    · exact ![714924299]
    · exact ![226981, 61, 61]
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
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
      exact NI31N2
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
      exact NI37N2
      exact NI37N3
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
      exact NI41N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
      exact NI61N2
  β := ![I29N1, I29N2, I31N0, I31N1, I31N2, I37N0, I37N1, I37N2, I37N3, I41N1, I41N2, I43N1, I53N1, I61N1, I61N2]
  Il := ![[I29N1, I29N2], [I31N0, I31N1, I31N2], [I37N0, I37N1, I37N2, I37N3], [I41N1, I41N2], [I43N1], [], [I53N1], [], [I61N1, I61N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
