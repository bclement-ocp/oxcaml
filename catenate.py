import pathlib
import textwrap

def main(*, files):
    for file in files:
        if file.suffix != '.ml':
            pass

        print(f'module {file.stem.capitalize()}', end='')

        mli_file = file.with_suffix('.mli')
        if mli_file.is_file():
            print(' : sig ')
            print(textwrap.indent(mli_file.open().read(), '  '))
            print('end = struct')
        else:
            print(' = struct')

        print(textwrap.indent(file.open().read(), '  '))
        print('end')

if __name__ == '__main__':
    import argparse

    parser = argparse.ArgumentParser()
    parser.add_argument('files', nargs='*', type=pathlib.Path)

    ns = parser.parse_args()
    main(**vars(ns))
