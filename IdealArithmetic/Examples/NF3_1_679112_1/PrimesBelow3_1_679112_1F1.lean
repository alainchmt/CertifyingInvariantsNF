
import IdealArithmetic.Examples.NF3_1_679112_1.RI3_1_679112_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-75700483542621, 14252093029084, -2384523843632]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-75700483542621, 14252093029084, -2384523843632]] 
 ![![37, 0, 0], ![0, 37, 0], ![1, 26, 1]] where
  M :=![![![-75700483542621, 14252093029084, -2384523843632], ![376754767293856, -70931435855357, 11867569185452], ![-1875075931301416, 353019628922952, -59063866669905]]]
  hmulB := by decide  
  f := ![![![-3719913, 846612, 320288]], ![![-50605504, -4360489, 1166900]], ![![-40644141, -4472038, 742327]]]
  g := ![![![-1981512424297, 2060803053068, -2384523843632], ![9861816165092, -10256438775057, 11867569185452], ![-49081407152203, 51045409792986, -59063866669905]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [13, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 36], [0, 1]]
 g := ![![[10, 26], [36], [1, 1], [28], [1]], ![[34, 11], [36], [19, 36], [28], [1]]]
 h' := ![![[18, 36], [34, 27], [24, 31], [27, 36], [24, 18], [0, 1]], ![[0, 1], [2, 10], [27, 6], [9, 1], [15, 19], [18, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [27, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [13, 19, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-461, -183, -17]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-12, 7, -17]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3719913, 846612, 320288]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-3719913, 846612, 320288]] 
 ![![37, 0, 0], ![10, 1, 0], ![11, 0, 1]] where
  M :=![![![-3719913, 846612, 320288], ![-50605504, -4360489, 1166900], ![-184370200, -52939304, -3193589]]]
  hmulB := by decide  
  f := ![![![-75700483542621, 14252093029084, -2384523843632]], ![![-10277028868442, 1934851200959, -323720790564]], ![![-73183277034331, 13778179790348, -2305233214861]]]
  g := ![![![-424573, 846612, 320288], ![-536122, -4360489, 1166900], ![10274387, -52939304, -3193589]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-75700483542621, 14252093029084, -2384523843632]] ![![-3719913, 846612, 320288]]
  ![![37, 0, 0]] where
 M := ![![![37, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-67995582699, 62191126619, 15241037149]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-67995582699, 62191126619, 15241037149]] 
 ![![41, 0, 0], ![0, 41, 0], ![12, 20, 1]] where
  M :=![![![-67995582699, 62191126619, 15241037149], ![-2408083869542, -98477656997, 77432163768], ![-12234281875344, -2562948197078, -21045493229]]]
  hmulB := by decide  
  f := ![![![-4890905741184931293737, 920808432889373782631, -154060856827233876145]], ![![24341615378702952430910, -4582784027530463541447, 766747576062139906486]], ![![7487690772244433362648, -1409703881203856410230, 235858165557260194659]]]
  g := ![![![-6119220207, -5917795521, 15241037149], ![-81396825238, -40173681277, 77432163768], ![-292237462356, -52244837378, -21045493229]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [18, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 40], [0, 1]]
 g := ![![[40, 16], [39], [37], [18, 37], [1]], ![[0, 25], [39], [37], [28, 4], [1]]]
 h' := ![![[18, 40], [31, 37], [6, 30], [4, 23], [23, 18], [0, 1]], ![[0, 1], [0, 4], [13, 11], [8, 18], [19, 23], [18, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [3, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [18, 23, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![470, -1458, 46]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2, -58, 46]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4890905741184931293737, -920808432889373782631, 154060856827233876145]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![4890905741184931293737, -920808432889373782631, 154060856827233876145]] 
 ![![41, 0, 0], ![20, 1, 0], ![10, 0, 1]] where
  M :=![![![4890905741184931293737, -920808432889373782631, 154060856827233876145], ![-24341615378702952430910, 4582784027530463541447, -766747576062139906486], ![121146117017818105224788, -22808120226578672617938, 3816036451468323634961]]]
  hmulB := by decide  
  f := ![![![67995582699, -62191126619, -15241037149]], ![![91902329842, -27935240863, -9323241628]], ![![314981407374, 47342364168, -3204021421]]]
  g := ![![![530889410504879711827, -920808432889373782631, 154060856827233876145], ![-2642190735821727419390, 4582784027530463541447, -766747576062139906486], ![13149955049627032225218, -22808120226578672617938, 3816036451468323634961]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-67995582699, 62191126619, 15241037149]] ![![4890905741184931293737, -920808432889373782631, 154060856827233876145]]
  ![![41, 0, 0]] where
 M := ![![![-41, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-710231565136230296390906445075, 133714949559264331899905648462, -22371905994681025103879973300]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-710231565136230296390906445075, 133714949559264331899905648462, -22371905994681025103879973300]] 
 ![![43, 0, 0], ![0, 43, 0], ![16, 16, 1]] where
  M :=![![![-710231565136230296390906445075, 133714949559264331899905648462, -22371905994681025103879973300], ![3534761147159601966413035781400, -665487753146868246183146498475, 111343043564583306796025675162], ![-17592200883204162473772056675596, 3312075060030435352820984431076, -554144709582284939387120823313]]]
  hmulB := by decide  
  f := ![![![465702982678759, -62272977254042, -31313708981008]], ![![4947566018999264, 528330400640775, -93586686235050]], ![![2358116289581076, 292829259666444, -36364246722121]]]
  g := ![![![-8192583005147299877414578425, 11434080127306063571208958634, -22371905994681025103879973300], ![40773777909913233899456394856, -56906429073958166393478076769, 111343043564583306796025675162], ![-202927570462502405664607523316, 283218381705744055418951572188, -554144709582284939387120823313]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [32, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 42], [0, 1]]
 g := ![![[33, 1], [28, 9], [23], [10, 17], [1]], ![[9, 42], [27, 34], [23], [32, 26], [1]]]
 h' := ![![[19, 42], [7, 1], [12, 3], [24, 25], [11, 19], [0, 1]], ![[0, 1], [26, 42], [26, 40], [26, 18], [28, 24], [19, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [13, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [32, 24, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2750, -260, 102]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![26, -44, 102]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![465702982678759, -62272977254042, -31313708981008]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![465702982678759, -62272977254042, -31313708981008]] 
 ![![43, 0, 0], ![26, 1, 0], ![12, 0, 1]] where
  M :=![![![465702982678759, -62272977254042, -31313708981008], ![4947566018999264, 528330400640775, -93586686235050], ![14786696425137900, 5134739391469364, 434743714405725]]]
  hmulB := by decide  
  f := ![![![-710231565136230296390906445075, 133714949559264331899905648462, -22371905994681025103879973300]], ![![-347238594101915947436058878850, 65374440358000101935218613059, -10937825867374961532671014666]], ![![-607325108484626186754951953872, 114340801273060635712089586340, -19130408872522261410085593091]]]
  g := ![![![57222439512929, -62272977254042, -31313708981008], ![-178278701461402, 528330400640775, -93586686235050], ![-2882173309905448, 5134739391469364, 434743714405725]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-710231565136230296390906445075, 133714949559264331899905648462, -22371905994681025103879973300]] ![![465702982678759, -62272977254042, -31313708981008]]
  ![![43, 0, 0]] where
 M := ![![![43, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5314533606854288437523515762885135, -1000564644061164893217596914594020, 167404902984439457053500095612526]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![5314533606854288437523515762885135, -1000564644061164893217596914594020, 167404902984439457053500095612526]] 
 ![![47, 0, 0], ![0, 47, 0], ![40, 35, 1]] where
  M :=![![![5314533606854288437523515762885135, -1000564644061164893217596914594020, 167404902984439457053500095612526], ![-26449974671541434214453015106779108, 4979723800885409523416515571660083, -833159741076725436164096818981494], ![131639239090122618913927297399076052, -24783655189387983342124821468816120, 4146564059808684087252418752678589]]]
  hmulB := by decide  
  f := ![![![-56924201844868519, -13646059552793220, -443730503104974]], ![![70109419490585892, -56036740838658571, -14089790055898194]], ![![51128690153354896, -51251900252391415, -12362093680323245]]]
  g := ![![![-29397074734538081800350809821615, -145951835074820125321065963000690, 167404902984439457053500095612526], ![146306701521863473023635269201716, 726389675288740421045955409276859, -833159741076725436164096818981494], ![-728155814940952012258924525703564, -3615178665589189923318286761969505, 4146564059808684087252418752678589]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [37, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 46], [0, 1]]
 g := ![![[1, 14], [25, 21], [31, 28], [25, 6], [1]], ![[0, 33], [0, 26], [29, 19], [38, 41], [1]]]
 h' := ![![[10, 46], [15, 22], [28, 16], [15, 34], [10, 10], [0, 1]], ![[0, 1], [0, 25], [0, 31], [26, 13], [16, 37], [10, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [37, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [37, 37, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-399, -1389, -131]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![103, 68, -131]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![56924201844868519, 13646059552793220, 443730503104974]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![56924201844868519, 13646059552793220, 443730503104974]] 
 ![![47, 0, 0], ![11, 1, 0], ![20, 0, 1]] where
  M :=![![![56924201844868519, 13646059552793220, 443730503104974], ![-70109419490585892, 56036740838658571, 14089790055898194], ![-2226186828831914652, -98288999602382280, 70126530894556765]]]
  hmulB := by decide  
  f := ![![![-5314533606854288437523515762885135, 1000564644061164893217596914594020, -167404902984439457053500095612526]], ![![-681061595826717842517141665637391, 128223133697604346850575542316471, -21453067909619331732434132611836]], ![![-5062338536749114631157396013974016, 953084001502367685244186377887160, -159460896159520706985583418402747]]]
  g := ![![![-2171426878679923, 13646059552793220, 443730503104974], ![-20602327017740299, 56036740838658571, 14089790055898194], ![-54202945768017976, -98288999602382280, 70126530894556765]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![5314533606854288437523515762885135, -1000564644061164893217596914594020, 167404902984439457053500095612526]] ![![56924201844868519, 13646059552793220, 443730503104974]]
  ![![47, 0, 0]] where
 M := ![![![-47, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![264696706651936515078029, 26676024813027145644494, -5326370520900401163690]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![264696706651936515078029, 26676024813027145644494, -5326370520900401163690]] 
 ![![53, 0, 0], ![0, 53, 0], ![44, 46, 1]] where
  M :=![![![264696706651936515078029, 26676024813027145644494, -5326370520900401163690], ![841566542302263383863020, 275349447693737317405409, 21349654292126744480804], ![-3373245378156025627967032, 798867233718009894901412, 296699101985864061886213]]]
  hmulB := by decide  
  f := ![![![1219630086751856250238875517387317194434759073, -229619160195596986086989988371602809732114934, 38417680920536866709683310065626540322484762]], ![![-6069993585444824940129962990368993370952592396, 1142794724910782516819508897256064113789789549, -191201479275060119377306678305976269409630172]], ![![-3685776365809825912714213577728065810225816676, 693919314535755163858386795314554429697810002, -116099940387045678465808289438438731590066019]]]
  g := ![![![9416169991916116344913, 5126208844800860361778, -5326370520900401163690], ![-1845627293421007043252, -13334616032907413749275, 21349654292126744480804], ![-309962374821397063225668, -242439461464749753808762, 296699101985864061886213]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [9, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [32, 52], [0, 1]]
 g := ![![[20, 6], [17], [50, 44], [11], [32, 1]], ![[0, 47], [17], [27, 9], [11], [11, 52]]]
 h' := ![![[32, 52], [46, 35], [27, 21], [6, 37], [30, 8], [0, 1]], ![[0, 1], [0, 18], [10, 32], [24, 16], [21, 45], [32, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [29, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [9, 21, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-465, -185, -19]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7, 13, -19]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1219630086751856250238875517387317194434759073, 229619160195596986086989988371602809732114934, -38417680920536866709683310065626540322484762]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-1219630086751856250238875517387317194434759073, 229619160195596986086989988371602809732114934, -38417680920536866709683310065626540322484762]] 
 ![![53, 0, 0], ![6, 1, 0], ![17, 0, 1]] where
  M :=![![![-1219630086751856250238875517387317194434759073, 229619160195596986086989988371602809732114934, -38417680920536866709683310065626540322484762], ![6069993585444824940129962990368993370952592396, -1142794724910782516819508897256064113789789549, 191201479275060119377306678305976269409630172], ![-30209833725459498861614455172344250566721567176, 5687590626894704701375349633757040832133332052, -951593245635722397442202218950087844380159377]]]
  hmulB := by decide  
  f := ![![![-264696706651936515078029, -26676024813027145644494, 5326370520900401163690]], ![![-45844278909695895742098, -8215199935318871533441, 200161676099540801912]], ![![-21256578017488587327537, -23629427463008893789770, -3889637794916174379311]]]
  g := ![![![-36683857967477574201815078801910997497079391, 229619160195596986086989988371602809732114934, -38417680920536866709683310065626540322484762], ![182572392211952792672317034767995876862785222, -1142794724910782516819508897256064113789789549, 191201479275060119377306678305976269409630172], ![-908647024736234836100926702881792494435072643, 5687590626894704701375349633757040832133332052, -951593245635722397442202218950087844380159377]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![264696706651936515078029, 26676024813027145644494, -5326370520900401163690]] ![![-1219630086751856250238875517387317194434759073, 229619160195596986086989988371602809732114934, -38417680920536866709683310065626540322484762]]
  ![![53, 0, 0]] where
 M := ![![![-53, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-248235758645746261, 93678159753725961, 28844304029355017]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-248235758645746261, 93678159753725961, 28844304029355017]] 
 ![![59, 0, 0], ![0, 59, 0], ![3, 25, 1]] where
  M :=![![![-248235758645746261, 93678159753725961, 28844304029355017], ![-4557400036638092686, -305924366704456295, 122522463783080978], ![-19358549277726794524, -4802444964204254642, -183401902921375317]]]
  hmulB := by decide  
  f := ![![![-10923974579670666608584435880282549, 2056651353741467043725351410859903, -344099226761064298965544681344947]], ![![54367677828248159236556059652501626, -10235776126148538010653346517592655, 1712552126980402744759806729514956]], ![![17895538744140480464679639328954745, -3369184330816977887934256991758728, 563699686356927804342457532301040]]]
  g := ![![![-5674045266674768, -10634397304748296, 28844304029355017], ![-83474024203175180, -57101456970872555, 122522463783080978], ![-318785484219706247, -3684701545252063, -183401902921375317]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [48, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 58], [0, 1]]
 g := ![![[24, 16], [22, 46], [35], [24, 17], [28, 1]], ![[0, 43], [12, 13], [35], [28, 42], [56, 58]]]
 h' := ![![[28, 58], [6, 4], [48, 20], [28, 25], [13, 28], [0, 1]], ![[0, 1], [0, 55], [18, 39], [20, 34], [30, 31], [28, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57]]
 b := ![[], [14, 58]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [48, 31, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6082, 391, 431]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-125, -176, 431]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10923974579670666608584435880282549, -2056651353741467043725351410859903, 344099226761064298965544681344947]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![10923974579670666608584435880282549, -2056651353741467043725351410859903, 344099226761064298965544681344947]] 
 ![![59, 0, 0], ![33, 1, 0], ![32, 0, 1]] where
  M :=![![![10923974579670666608584435880282549, -2056651353741467043725351410859903, 344099226761064298965544681344947], ![-54367677828248159236556059652501626, 10235776126148538010653346517592655, -1712552126980402744759806729514956], ![270583236062903633672049463263363048, -50942573574287353747036446193471714, 8523223999168135265893539788077699]]]
  hmulB := by decide  
  f := ![![![248235758645746261, -93678159753725961, -28844304029355017]], ![![216087797829622361, -47211100087601702, -18209906724606721]], ![![462747348379502964, 30588878848898710, -12535861457931953]]]
  g := ![![![1148852440623474940417349197213916, -2056651353741467043725351410859903, 344099226761064298965544681344947], ![-5717739354708085182301740328620011, 10235776126148538010653346517592655, -1712552126980402744759806729514956], ![28456694848152643708739981600499038, -50942573574287353747036446193471714, 8523223999168135265893539788077699]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-248235758645746261, 93678159753725961, 28844304029355017]] ![![10923974579670666608584435880282549, -2056651353741467043725351410859903, 344099226761064298965544681344947]]
  ![![59, 0, 0]] where
 M := ![![![-59, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0]] 
 ![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [28, 60, 58, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [33, 39, 25], [31, 21, 36], [0, 1]]
 g := ![![[1, 21, 25], [6, 9], [55, 52, 15], [2, 33, 9], [1]], ![[24, 5, 43, 52], [31, 36], [8, 7, 34, 60], [33, 15, 55, 47], [56, 13, 13, 9]], ![[47, 31, 58, 52], [34, 20], [54, 11, 43, 58], [48, 30, 55, 9], [9, 40, 3, 52]]]
 h' := ![![[33, 39, 25], [57, 42, 56], [46, 27, 3], [5, 45, 36], [33, 1, 3], [0, 1]], ![[31, 21, 36], [5, 47, 30], [43, 19, 6], [34, 22, 51], [26, 42, 27], [33, 39, 25]], ![[0, 1], [58, 33, 36], [41, 15, 52], [19, 55, 35], [15, 18, 31], [31, 21, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48, 44], []]
 b := ![[], [24, 40, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [28, 60, 58, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![19459, -5917, -915]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![319, -97, -15]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def PBC61 : ContainsPrimesAboveP 61 ![I61N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![61, 0, 0]]) timesTableT_eq_Table B_one_repr 61 (by decide) 𝕀


def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2275, -1990, -308]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-2275, -1990, -308]] 
 ![![67, 0, 0], ![9, 1, 0], ![53, 0, 1]] where
  M :=![![![-2275, -1990, -308], ![48664, -1659, -2298], ![363084, 53260, -3957]]]
  hmulB := by decide  
  f := ![![![128956143, -24278510, 4062048]], ![![7743309, -1457829, 243910]], ![![149684725, -28181070, 4714987]]]
  g := ![![![477, -1990, -308], ![2767, -1659, -2298], ![1395, 53260, -3957]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6889, 1297, -217]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-6889, 1297, -217]] 
 ![![67, 0, 0], ![62, 1, 0], ![42, 0, 1]] where
  M :=![![![-6889, 1297, -217], ![34286, -6455, 1080], ![-170640, 32126, -5375]]]
  hmulB := by decide  
  f := ![![![455, -33, -25]], ![![480, -23, -24]], ![![422, 40, -9]]]
  g := ![![![-1167, 1297, -217], ![5808, -6455, 1080], ![-28906, 32126, -5375]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-2275, -1990, -308]] ![![-6889, 1297, -217]]
  ![![455, -33, -25]] where
 M := ![![![455, -33, -25]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![455, -33, -25]] ![![-6889, 1297, -217]]
  ![![67, 0, 0]] where
 M := ![![![67, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0 ⊙ MulI67N1)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3548804352518141804592623307894537927018792367, -668131660554457719835254215511416558451844160, 111785396855492015113313467669448535316643544]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![3548804352518141804592623307894537927018792367, -668131660554457719835254215511416558451844160, 111785396855492015113313467669448535316643544]] 
 ![![71, 0, 0], ![2, 1, 0], ![67, 0, 1]] where
  M :=![![![3548804352518141804592623307894537927018792367, -668131660554457719835254215511416558451844160, 111785396855492015113313467669448535316643544], ![-17662092703167738387903527891772868580029679952, 3325233558807157774365996372555640856385505279, -556346263698965704721940747841968023135200616], ![87902709664436581346066638159030947655361697328, -16549400175769806978459646396088932533759278720, 2768887295108192069644055624713672833250304663]]]
  hmulB := by decide  
  f := ![![![-497249224075134714875543, -28708369498922587265600, 14306616167329994733784]], ![![-45844278909695895742098, -8215199935318871533441, 200161676099540801912]], ![![-437186211079470370093443, -58522571890179821544640, 5891254555911582398431]]]
  g := ![![![-36683857967477574201815078801910997497079391, -668131660554457719835254215511416558451844160, 111785396855492015113313467669448535316643544], ![182572392211952792672317034767995876862785222, 3325233558807157774365996372555640856385505279, -556346263698965704721940747841968023135200616], ![-908647024736234836100926702881792494435072643, -16549400175769806978459646396088932533759278720, 2768887295108192069644055624713672833250304663]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17401189, 1804773, 1065149]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-17401189, 1804773, 1065149]] 
 ![![71, 0, 0], ![19, 1, 0], ![65, 0, 1]] where
  M :=![![![-17401189, 1804773, 1065149], ![-168293542, -19531487, 2869922], ![-453447676, -174033386, -16661565]]]
  hmulB := by decide  
  f := ![![![824887383413047, -155301144414769, 25983501584269]], ![![162922070908921, -30673258642762, 5131956158741]], ![![1042955880127705, -196356793684697, 32852540005514]]]
  g := ![![![-1703191, 1804773, 1065149], ![229011, -19531487, 2869922], ![55439273, -174033386, -16661565]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8768066215000249, -1947495540678769, -37321889666859]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![-8768066215000249, -1947495540678769, -37321889666859]] 
 ![![71, 0, 0], ![49, 1, 0], ![13, 0, 1]] where
  M :=![![![-8768066215000249, -1947495540678769, -37321889666859], ![5896858567363722, -8693422435666531, -1984817430345628], ![313601153994609224, 9866493428054978, -10678239866012159]]]
  hmulB := by decide  
  f := ![![![-112413638157012982652738441286613, 21164060700477592749636823726373, -3540968141688260827854185375803]], ![![-69701342300097055481453835685453, 13122637640137543432889778761370, -2195554174421626037226372465687]], ![![-59800365075068777720102205579099, 11258585498244721869051756635473, -1883678805025274927286645662956]]]
  g := ![![![1227385913294769, -1947495540678769, -37321889666859], ![6446157528303055, -8693422435666531, -1984817430345628], ![-437181770731361, 9866493428054978, -10678239866012159]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![3548804352518141804592623307894537927018792367, -668131660554457719835254215511416558451844160, 111785396855492015113313467669448535316643544]] ![![-17401189, 1804773, 1065149]]
  ![![112413638157012982652738441286613, -21164060700477592749636823726373, 3540968141688260827854185375803]] where
 M := ![![![112413638157012982652738441286613, -21164060700477592749636823726373, 3540968141688260827854185375803]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![112413638157012982652738441286613, -21164060700477592749636823726373, 3540968141688260827854185375803]] ![![-8768066215000249, -1947495540678769, -37321889666859]]
  ![![71, 0, 0]] where
 M := ![![![-71, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1, I71N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
    exact isPrimeI71N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0 ⊙ MulI71N1)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-64958069755700829, 12229624037034548, -2046143682577280]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-64958069755700829, 12229624037034548, -2046143682577280]] 
 ![![73, 0, 0], ![0, 73, 0], ![26, 21, 1]] where
  M :=![![![-64958069755700829, 12229624037034548, -2046143682577280], ![323290701847210240, -60865782390546269, 10183480354457268], ![-1608989896004248344, 302923741138295704, -50682302036089001]]]
  hmulB := by decide  
  f := ![![![-264061789, -32435636, 4143472]], ![![-654668576, -272348733, -28292164]], ![![-221143626, -98092249, -10781453]]]
  g := ![![![-161073068612213, 756145772207636, -2046143682577280], ![801646748374264, -3763272189508889, 10183480354457268], ![-3989726617341566, 18729480601317325, -50682302036089001]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [32, 46, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 72], [0, 1]]
 g := ![![[6, 16], [32], [18], [39, 9], [72], [1]], ![[0, 57], [32], [18], [63, 64], [72], [1]]]
 h' := ![![[27, 72], [35, 69], [57, 18], [66, 23], [34, 70], [41, 27], [0, 1]], ![[0, 1], [0, 4], [32, 55], [30, 50], [26, 3], [40, 46], [27, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47]]
 b := ![[], [66, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [32, 46, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1232, -602, 93]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-50, -35, 93]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![264061789, 32435636, -4143472]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![264061789, 32435636, -4143472]] 
 ![![73, 0, 0], ![51, 1, 0], ![27, 0, 1]] where
  M :=![![![264061789, 32435636, -4143472], ![654668576, 272348733, 28292164], ![-4470161912, 598084248, 300640897]]]
  hmulB := by decide  
  f := ![![![64958069755700829, -12229624037034548, 2046143682577280]], ![![40953025420459343, -7710206075318023, 1289997910369644]], ![![46066544923399599, -8672925892304500, 1451070978981857]]]
  g := ![![![-17510711, 32435636, -4143472], ![-191767195, 272348733, 28292164], ![-590270723, 598084248, 300640897]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-64958069755700829, 12229624037034548, -2046143682577280]] ![![264061789, 32435636, -4143472]]
  ![![73, 0, 0]] where
 M := ![![![-73, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5933021572153140832008372720535465487745568087, -1117007070929485072796376317452926242543823707, 186886935743506456024811856536986073136207697]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![5933021572153140832008372720535465487745568087, -1117007070929485072796376317452926242543823707, 186886935743506456024811856536986073136207697]] 
 ![![79, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![5933021572153140832008372720535465487745568087, -1117007070929485072796376317452926242543823707, 186886935743506456024811856536986073136207697], ![-29528135847474020051920273332843799555520816126, 5559247700666127919958749007461493341473152693, -930120135185978616771564460915940169407616010], ![146958981359384621449907184824718546766403329580, -27667895577102062818377144411011919216705584106, 4629127565480149303187184546545553172065536683]]]
  hmulB := by decide  
  f := ![![![-603156515980494955399741, -7109367042984224520001, 22922139454847947871049]], ![![-45844278909695895742098, -8215199935318871533441, 200161676099540801912]], ![![-31625544823727446702096, -46244602261894977345922, -8015038259219330731529]]]
  g := ![![![75101538888014440911498388867537537819564153, -1117007070929485072796376317452926242543823707, 186886935743506456024811856536986073136207697], ![-373773871487012912049623713073972146272415394, 5559247700666127919958749007461493341473152693, -930120135185978616771564460915940169407616010], ![1860240270371957233543128921831880338815232020, -27667895577102062818377144411011919216705584106, 4629127565480149303187184546545553172065536683]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N0 : Nat.card (O ⧸ I79N0) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N0)

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := prime_ideal_of_norm_prime hp79.out _ NI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-59456506261, -445188626, 2310924728]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-59456506261, -445188626, 2310924728]] 
 ![![79, 0, 0], ![12, 1, 0], ![14, 0, 1]] where
  M :=![![![-59456506261, -445188626, 2310924728], ![-365126107024, -64078355717, 1865736102], ![-294786304116, -368857579228, -62212619615]]]
  hmulB := by decide  
  f := ![![![-4674673271838386478211, 880098451594466848974, -147249652264267494124]], ![![-415577648155776881860, 78240600655996844275, -13090468706848235122]], ![![-2294120710125429224826, 431912984574891155032, -72263548097207557631]]]
  g := ![![![-1094521379, -445188626, 2310924728], ![4780934888, -64078355717, 1865736102], ![63322548370, -368857579228, -62212619615]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6324472646621, 712592825303, -112151668057]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![6324472646621, 712592825303, -112151668057]] 
 ![![79, 0, 0], ![66, 1, 0], ![68, 0, 1]] where
  M :=![![![6324472646621, 712592825303, -112151668057], ![17719963553006, 6548775982735, 600441157246], ![-94869702844868, 16519081238514, 7149217139981]]]
  hmulB := by decide  
  f := ![![![-36899885246170946228855591, 6947123356152132601686541, -1162326210865479713591433]], ![![-28503099809247299447557248, 5366264666855705884932139, -897832060402974787454930]], ![![-43331520831581208859255788, 8158004243601487416277734, -1364919215417796891617659]]]
  g := ![![![-418738486019, 712592825303, -112151668057], ![-5763661392408, 6548775982735, 600441157246], ![-21155390254500, 16519081238514, 7149217139981]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![5933021572153140832008372720535465487745568087, -1117007070929485072796376317452926242543823707, 186886935743506456024811856536986073136207697]] ![![-59456506261, -445188626, 2310924728]]
  ![![-36899885246170946228855591, 6947123356152132601686541, -1162326210865479713591433]] where
 M := ![![![-36899885246170946228855591, 6947123356152132601686541, -1162326210865479713591433]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![-36899885246170946228855591, 6947123356152132601686541, -1162326210865479713591433]] ![![6324472646621, 712592825303, -112151668057]]
  ![![79, 0, 0]] where
 M := ![![![79, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1, I79N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
    exact isPrimeI79N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0 ⊙ MulI79N1)


lemma PB234I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB234I1 : PrimesBelowBoundCertificateInterval O 31 79 234 where
  m := 11
  g := ![2, 2, 2, 2, 2, 2, 1, 3, 3, 2, 3]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB234I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0]
    · exact ![I67N0, I67N1, I67N1]
    · exact ![I71N0, I71N1, I71N2]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1, I79N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
    · exact PBC67
    · exact PBC71
    · exact PBC73
    · exact PBC79
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![1369, 37]
    · exact ![1681, 41]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![226981]
    · exact ![67, 67, 67]
    · exact ![71, 71, 71]
    · exact ![5329, 73]
    · exact ![79, 79, 79]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
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
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
      exact NI71N2
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
      exact NI79N2
  β := ![I37N1, I41N1, I43N1, I47N1, I53N1, I59N1, I67N0, I67N1, I71N0, I71N1, I71N2, I73N1, I79N0, I79N1, I79N2]
  Il := ![[I37N1], [I41N1], [I43N1], [I47N1], [I53N1], [I59N1], [], [I67N0, I67N1, I67N1], [I71N0, I71N1, I71N2], [I73N1], [I79N0, I79N1, I79N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
