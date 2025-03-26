import json

def statement_to_lhs_rhs(s):


def main():
    list_of_dicts = []
    with open("amgm_valid.jsonl", "r") as file:
        for line in file:
            list_of_dicts.append(json.loads(line))

if __name__ == '__main__':
    #main()
    statement_to_lhs_rhs("theorem amgm_p2 (x y: ℝ) (hx : x > 0) (hy : y > 0) : (2 * x + y) / 3 ≥ (x * x * y) ^ (3⁻¹: ℝ ) := by\n")