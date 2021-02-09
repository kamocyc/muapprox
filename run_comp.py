import sys
import os

def run_command(com):
    stream = os.popen(com)
    output = stream.read()
    stream.close()
    return output
    
# def replace_file(path, replacer):
#     with open(path, 'r') as f:
#         text = f.read()
    
#     with open(path, 'w') as f:
#         f.write(replacer(text))

def main():
    if len(sys.argv) != 2:
        raise ValueError("Arugment should be one")
        
    bench = os.path.basename(sys.argv[1])
    
    comp_files = ["prover_exists_encoded.txt", "prover_elim_mu.txt", "disprover_exists_encoded.txt", "disprover_elim_mu.txt"]
    
    for _, e in enumerate(comp_files):
        path1 = "muapprox_" + e
        path2 = "../fptprove_muarith/sas_" + e
        
        if os.path.isfile(path1):
            os.remove(path1)
        if os.path.isfile(path2):
            os.remove(path2)
        
    print("START")
    
    run_command("cd ../fptprove_muarith && dune exec bin/main.exe -- --format hes --algorithm rec-limit --verbose benchmarks/hes/" + bench)
    
    print("fptprove_muarith: FINISHED")
    
    run_command("dune exec bin/muapprox_main.exe -- --hes --first-order-solver --dry-run --no-inlining benchmark/hes/" + bench)
    
    print("muapprox: FINISHED")
    
    results = []
    for _, e in enumerate(comp_files):
        path1 = "muapprox_" + e
        path2 = "../fptprove_muarith/sas_" + e
        
        # replace_file(path2, lambda text: text.replace("'", "_ap_").replace('#', '_sh_'))
        
        output = run_command("dune exec bin2/check_formula_equality.exe " + path1 + " " + path2)
        
        results.append((e, output))
    
    if all([ r[1] == '(func) Equal\n' for r in results ]):
        print("all equal")
    else:
        print("not all equal")
        print(results)
    
main()
