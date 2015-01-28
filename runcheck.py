#!/usr/bin/env python2

import argparse
import collections
import errno
import glob
import logging
import os
import re
import string
import subprocess

LOCKFILE = '.runcheck.lock'
LOGFILE = 'runcheck_make.log'

NOSTASH = 'NOSTASH'

logger = logging.getLogger("runcheck")

def admitted_faster_to_qed(s):
    """Replaces instances of "Admitted. (* faster *)" with "Qed."

    >>> admitted_faster_to_qed('asd Admitted. (* faster *)')
    'asd Qed.'

    >>> admitted_faster_to_qed('asd Admitted.  (*   faStEr*)')
    'asd Qed.'

    >>> admitted_faster_to_qed('asd Admitted. (* a lot faster *)')
    'asd Admitted. (* a lot faster *)'

    >>> admitted_faster_to_qed('asd Admitted.(*  otheRwise proof 	tOo   sLow*) asd2')
    'asd Qed. asd2'
    """

    result = s
    result = re.sub(
        r'Admitted[.]\s*[(][*]\s*(?i)faster\s*[*][)]',
        'Qed.',
        result)
    result = re.sub(
        r'Admitted[.]\s*[(][*]\s*(?i)otherwise\s*proof\s*too\s*slow[*][)]',
        'Qed.',
        result)
    return result

def admitted_to_qed(s):
    """Replaces instances of "Admitted." with "Qed."

    >>> admitted_to_qed('asd Admitted. ')
    'asd Qed. '

    >>> admitted_to_qed('asd Admitted Admi tted. foo')
    'asd Admitted Admi tted. foo'
    """

    return string.replace(s, "Admitted.", "Qed.")

def transform_file(path, transform):
    """Read the content of the specfied path, apply the transform
    and write back the transformed content.
    """

    with open(path) as fr:
        content = fr.read()
    with open(path, 'w') as fw:
        fw.write(transform(content))

def transform_all(transform):
    for path in glob.glob(r'coq/*.v'):
        transform_file(path, transform)

def start(args):
    # Acquire lock, save state, transform coq sources
    try:
        with os.fdopen(os.open(LOCKFILE, 
                               os.O_EXCL | os.O_CREAT | os.O_RDWR), 'w') as f:
            rev = subprocess.check_output(['git', 'stash', 'create'])
            if rev == '':
                f.write(NOSTASH)
                logger.info('No need to stash.')
            else:
                f.write(rev)
                logger.info('Stashed working tree and index in {0}.'.format(rev))

            patch(args)

    except OSError as err:
        if err.errno == errno.EEXIST:
            logger.error('Could not create lock. '
                          'You should probably run "runcheck.py reset". '
                          'If you believe that this is a mistake, you can '
                          'delete the lockfile {0}'.format(LOCKFILE))
            exit(1)
        else:
            raise
    except subprocess.CalledProcessError:
        logger.error('Failed to save current state.')
        os.remove(LOCKFILE)
        exit(1)

    # Unleash the roosters
    kontinue(None)

def patch(args):
    transform = admitted_faster_to_qed
    if args.all:
        transform = admitted_to_qed
    logger.info('Start transforming coq source.')
    transform_all(transform)
    logger.info('Done transforming coq source.')

def kontinue(args):
    try:
        with os.fdopen(os.open(LOCKFILE, os.O_RDWR)):
            logger.info('Running make')
            subprocess.check_call('echo "make :" >> ' + LOGFILE, shell=True)
            subprocess.check_call('make >> ' + LOGFILE, shell=True)
            logger.info('make done')
    except OSError:
        logger.error('Could not find/acquire lock. Aborting...')
        exit(1)
    except subprocess.CalledProcessError:
        logger.error('make complained. Check {0} for details. '
                      'Then you can either "runcheck.py continue" or '
                      '"runcheck.py reset".'.format(LOGFILE))
        exit(1)

    # Everything went well, reset
    reset(None)

def reset(args):
    try:
        with os.fdopen(os.open(LOCKFILE, os.O_RDWR)) as f:
            rev = f.read(40) #40 = length of a sha1 in hex
            if rev != NOSTASH and len(rev) != 40:
                raise Exception('Could not read revision from lock!')
            logger.info('Restoring HEAD')
            subprocess.check_call(['git', 'reset', '--hard', 'HEAD'])
            if rev != NOSTASH:
                logger.info('Applying stash {0}'.format(rev))
                subprocess.check_call(['git', 'stash', 'apply', '--index', rev])
            logger.info('Your tree is back in its old state. :)')
    except OSError:
        logger.error('Could not find/acquire lock. Aborting...')
        exit(1)
    else:
        os.remove(LOCKFILE)
        logger.info('Removed lock')


def main():
    import doctest
    doctest.testmod()

    parser = argparse.ArgumentParser(description='''\
                check whether everything still works after "Admitted." has \
                been replaced with "Qed.".
                If something goes wrong "runcheck.py reset" should get you
                back into your old state.''',
                epilog='''Details:
                runcheck.py has three stages:

                1. start: Save the current git working tree (tracked files \
                only) and index. Replace instances of "Admitted. (* faster \
                *)" with "Qed.". If successful, GOTO 2.
                2. continue: Run make on the sources. If \
                successful, GOTO 3. If this fails, you can either make manual \
                adjustments and call "runcheck.py continue" or get back \
                to the old state by manually calling "runcheck.py reset".
                3. reset: Reset the working tree and index back to their
                previous state.''')

    parser.add_argument('--all', '-a',
                              action='store_true',
                              help='process all instances of "Admitted.", not'
                              'just "Admitted. (* faster *) and its likes.')
    subparsers = parser.add_subparsers()
    parser_start = subparsers.add_parser('start',
                                         help='start the check')
    parser_start.set_defaults(func=start)
    parser_continue = subparsers.add_parser('continue',
                                            help='continue an interrupted check')
    parser_continue.set_defaults(func=kontinue)
    parser_reset = subparsers.add_parser('reset',
                                         help='reset to pre-check state')
    parser_reset.set_defaults(func=reset)
    parser_reset = subparsers.add_parser('patch',
                                         help='just patch the coq source')
    parser_reset.set_defaults(func=patch)

    args = parser.parse_args()
    args.func(args)

if __name__ == '__main__':
    # Logging setup
    formatter = logging.Formatter(fmt='runcheck.py: %(message)s')
    handler = logging.StreamHandler()
    handler.setFormatter(formatter)
    logger.setLevel(logging.INFO)
    logger.addHandler(handler)
    main()
