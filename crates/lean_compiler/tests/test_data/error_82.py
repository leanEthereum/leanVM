# Error: derived fp-relative pointer with a negative resolved offset
# directly used as an `hint_witness` destination.
def main():
    buf = Array(8)
    ptr = buf - 3
    hint_witness("payload", ptr)
    return
