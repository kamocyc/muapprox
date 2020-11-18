
def get_last_line(text, nth):
    try:
        return text.strip(' \n\r').split("\n")[nth]
    except IndexError:
        return text.strip(' \n\r')

print(get_last_line('aaa\nbbb\n', -3))
