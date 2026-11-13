# SnapClean

Breathes new life into old documents. SnapClean turns pages you can only look at - scans, screen
snapshots, a PDF whose pages are pictures - into a searchable PDF, a Word document (.docx) or an
editable web page (.html).

It is one Python file with a desktop window. Everything runs on your own computer; nothing is uploaded.

## What it does

The window has three tabs, and they are the three steps:

1. **Snapshot** - takes a picture of each page off the screen, turning the pages itself.
2. **Remove watermark** - finds what is printed on every page (a stamp, a watermark, a logo) and
   takes it out, putting back the text underneath where it can.
3. **Make PDF / Word / HTML** - reads the text and rebuilds each page:
   - a PDF that looks like the original, with text you can search and copy, and confirmed words
     re-typeset as real type;
   - a Word file in one of four layouts, from an exact page copy to a structured document with
     real heading styles, lists and paragraphs rejoined across columns and pages;
   - a single web page in which every paragraph, picture and table can be edited, restyled and moved.

You do not have to use all three: pictures you already have (PNG, JPG, TIFF, BMP, WebP, GIF) go
straight to tab 2 or 3, and a PDF goes straight to tab 3.

## It tells you what it is not sure of

Each word is read several times by two OCR engines (RapidOCR and Tesseract), and the readings vote.
In the default *Strict* mode a word is replaced with real text only when the readings agree and it
passes the checks. Anything else is left as a picture of itself, or typed in and highlighted in
yellow, so you know where to proof-read. A review window lets you settle the leftovers quickly.

## Requirements

- **Python 3.12 or 3.13** - what the program is made for and tested on. Get it from
  [python.org](https://www.python.org/downloads/).
- A newer Python (3.14 and later) also works on Windows: the first time it starts, the program
  installs Python 3.13 beside yours and restarts itself in that, because the better text reader
  has no build for the newest Pythons yet. Python older than 3.10 is refused with a message.
- **Windows 10 or 11.** That is where it was developed and is used.
- **An internet connection for the first start**, which installs the Python packages the program
  uses and the Tesseract text reader. After that it runs offline.
- A graphics card is used for reading when one is found (DirectML or CUDA). It is not required.

Not sure which Python you have? Run `python --version`. Once the program is open, the line at the
bottom of its window says which Python it is running in.

## Running it

```
python snapclean.py
```

**Help > How to use this program...** (or F1) explains every tab and option. The same text is in
[HELP.html](HELP.html).

There is a command line as well: `python snapclean.py run --help`, `python snapclean.py rebuild --help`.

## Limits

- It reads print. Handwriting mostly stays a picture.
- It is only as good as the pictures: letters about 16 pixels high or more read well. Zoom in
  before taking snapshots.
- Typewritten and photographed pages are a work in progress.
- Figures, formulas and tables without ruled lines are kept as pictures.
- Proof-read anything that matters. A confirmed word can still, rarely, be wrong.

## Use it on documents you have the right to work with

Removing a watermark or copying a document does not change who owns it. Respect copyright and the
terms you received a document under.

## About

Created by Doug Millner of NERX Power Consultants LLC - power engineering and training services.

- www.nerxpower.com
- douglas.millner@nerxpower.com

Released under the [MIT licence](LICENSE).
