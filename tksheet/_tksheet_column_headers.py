from ._tksheet_vars import *
from ._tksheet_other_classes import *

from collections import defaultdict, deque
from itertools import islice, repeat, accumulate, chain
from math import floor, ceil
from tkinter import ttk
import bisect
import csv as csv_module
import io
import pickle
import re
import tkinter as tk
import zlib
# for mac bindings
from platform import system as get_os


class ColumnHeaders(tk.Canvas):
    def __init__(self,
                 parentframe = None,
                 main_canvas = None,
                 row_index_canvas = None,
                 max_colwidth = None,
                 max_header_height = None,
                 header_align = None,
                 header_background = None,
                 header_border_color = None,
                 header_grid_color = None,
                 header_foreground = None,
                 header_select_background = None,
                 header_select_foreground = None,
                 drag_and_drop_color = None,
                 resizing_line_color = None):
        tk.Canvas.__init__(self,parentframe,
                           background = header_background,
                           highlightthickness = 0)
        self.parentframe = parentframe
        self.extra_motion_func = None
        self.extra_b1_press_func = None
        self.extra_b1_motion_func = None
        self.extra_b1_release_func = None
        self.extra_double_b1_func = None
        self.ch_extra_drag_drop_func = None
        self.selection_binding_func = None
        self.drag_selection_binding_func = None
        self.max_cw = float(max_colwidth)
        self.max_header_height = float(max_header_height)
        self.current_height = None    # is set from within MainTable() __init__ or from Sheet parameters
        self.MT = main_canvas         # is set from within MainTable() __init__
        self.RI = row_index_canvas    # is set from within MainTable() __init__
        self.TL = None                # is set from within TopLeftRectangle() __init__
        self.text_color = header_foreground
        self.grid_color = header_grid_color
        self.header_border_color = header_border_color
        self.selected_cells_background = header_select_background
        self.selected_cells_foreground = header_select_foreground
        self.drag_and_drop_color = drag_and_drop_color
        self.resizing_line_color = resizing_line_color
        self.align = header_align
        self.width_resizing_enabled = False
        self.height_resizing_enabled = False
        self.double_click_resizing_enabled = False
        self.col_selection_enabled = False
        self.drag_and_drop_enabled = False
        self.rc_delete_col_enabled = False
        self.rc_insert_col_enabled = False
        self.dragged_col = None
        self.visible_col_dividers = []
        self.col_height_resize_bbox = tuple()
        self.selected_cells = defaultdict(int)
        self.highlighted_cells = {}
        self.rsz_w = None
        self.rsz_h = None
        self.new_col_height = 0
        self.currently_resizing_width = False
        self.currently_resizing_height = False
        self.bind("<Motion>", self.mouse_motion)
        self.bind("<ButtonPress-1>", self.b1_press)
        self.bind("<Shift-ButtonPress-1>",self.shift_b1_press)
        self.bind("<B1-Motion>", self.b1_motion)
        self.bind("<ButtonRelease-1>", self.b1_release)
        self.bind("<Double-Button-1>", self.double_b1)
        
    def basic_bindings(self, onoff = "enable"):
        if onoff == "enable":
            self.bind("<Motion>", self.mouse_motion)
            self.bind("<ButtonPress-1>", self.b1_press)
            self.bind("<B1-Motion>", self.b1_motion)
            self.bind("<ButtonRelease-1>", self.b1_release)
            self.bind("<Double-Button-1>", self.double_b1)
        elif onoff == "disable":
            self.unbind("<Motion>")
            self.unbind("<ButtonPress-1>")
            self.unbind("<B1-Motion>")
            self.unbind("<ButtonRelease-1>")
            self.unbind("<Double-Button-1>")

    def set_height(self, new_height,set_TL = False):
        self.current_height = new_height
        self.config(height = new_height)
        if set_TL:
            self.TL.set_dimensions(new_h = new_height)

    def enable_bindings(self, binding):
        if binding == "column_width_resize":
            self.width_resizing_enabled = True
        if binding == "column_height_resize":
            self.height_resizing_enabled = True
        if binding == "double_click_column_resize":
            self.double_click_resizing_enabled = True
        if binding == "column_select":
            self.col_selection_enabled = True
        if binding == "drag_and_drop":
            self.drag_and_drop_enabled = True
        if binding == "rc_delete_column":
            self.rc_delete_col_enabled = True
            self.ch_rc_popup_menu.entryconfig("Delete Columns", state = "normal")
        if binding == "rc_insert_column":
            self.rc_insert_col_enabled = True
            self.ch_rc_popup_menu.entryconfig("Insert Column", state = "normal")

    def disable_bindings(self, binding):
        if binding == "column_width_resize":
            self.width_resizing_enabled = False
        if binding == "column_height_resize":
            self.height_resizing_enabled = False
        if binding == "double_click_column_resize":
            self.double_click_resizing_enabled = False
        if binding == "column_select":
            self.col_selection_enabled = False
        if binding == "drag_and_drop":
            self.drag_and_drop_enabled = False
        if binding == "rc_delete_column":
            self.rc_delete_col_enabled = False
            self.ch_rc_popup_menu.entryconfig("Delete Columns", state = "disabled")
        if binding == "rc_insert_column":
            self.rc_insert_col_enabled = False
            self.ch_rc_popup_menu.entryconfig("Insert Column", state = "disabled")

    def check_mouse_position_width_resizers(self, event):
        x = self.canvasx(event.x)
        y = self.canvasy(event.y)
        ov = None
        for x1, y1, x2, y2 in self.visible_col_dividers:
            if x >= x1 and y >= y1 and x <= x2 and y <= y2:
                ov = self.find_overlapping(x1, y1, x2, y2)
                break
        return ov

    def rc(self, event):
        self.focus_set()
        if self.MT.identify_col(x = event.x, allow_end = False) is None:
            self.MT.deselect("all")
            self.ch_rc_popup_menu.tk_popup(event.x_root, event.y_root)
        elif self.col_selection_enabled and all(v is None for v in (self.RI.rsz_h, self.RI.rsz_w, self.rsz_h, self.rsz_w)):
            c = self.MT.identify_col(x = event.x)
            if c < len(self.MT.col_positions) - 1:
                cols_selected = self.MT.anything_selected(exclude_rows = True, exclude_cells = True)
                if cols_selected:
                    x1 = self.MT.get_min_selected_cell_x()
                    x2 = self.MT.get_max_selected_cell_x()
                else:
                    x1 = None
                    x2 = None
                if all(e is not None for e in (x1, x2)) and c >= x1 and c <= x2:
                    self.ch_rc_popup_menu.tk_popup(event.x_root, event.y_root)
                else:
                    self.select_col(c, redraw = True)
                    self.ch_rc_popup_menu.tk_popup(event.x_root, event.y_root)
        

    def shift_b1_press(self, event):
        x = event.x
        c = self.MT.identify_col(x = x)
        if self.drag_and_drop_enabled or self.col_selection_enabled and self.rsz_h is None and self.rsz_w is None:
            if c < len(self.MT.col_positions) - 1:
                if c not in self.MT.selected_cols and self.col_selection_enabled:
                    c = int(c)
                    if self.MT.currently_selected and self.MT.currently_selected[0] == "column":
                        min_c = int(self.MT.currently_selected[1])
                        self.selected_cells = defaultdict(int)
                        self.RI.selected_cells = defaultdict(int)
                        self.MT.selected_cols = set()
                        self.MT.selected_rows = set()
                        self.MT.selected_cells = set()
                        if c > min_c:
                            for i in range(min_c, c + 1):
                                self.selected_cells[i] += 1
                                self.MT.selected_cols.add(i)
                        elif c < min_c:
                            for i in range(c, min_c + 1):
                                self.selected_cells[i] += 1
                                self.MT.selected_cols.add(i)
                    else:
                        self.select_col(c)
                    self.MT.main_table_redraw_grid_and_text(redraw_header = True, redraw_row_index = True)
                    if self.selection_binding_func is not None:
                        self.selection_binding_func(("column", c))
                elif c in self.MT.selected_cols:
                    self.dragged_col = c

    def mouse_motion(self, event):
        if not self.currently_resizing_height and not self.currently_resizing_width:
            x = self.canvasx(event.x)
            y = self.canvasy(event.y)
            mouse_over_resize = False
            if self.width_resizing_enabled and not mouse_over_resize:
                ov = self.check_mouse_position_width_resizers(event)
                if ov is not None:
                    for itm in ov:
                        tgs = self.gettags(itm)
                        if "v" == tgs[0]:
                            break
                    c = int(tgs[1])
                    self.rsz_w = c
                    self.config(cursor = "sb_h_double_arrow")
                    mouse_over_resize = True
                else:
                    self.rsz_w = None
            if self.height_resizing_enabled and not mouse_over_resize:
                try:
                    x1, y1, x2, y2 = self.col_height_resize_bbox[0], self.col_height_resize_bbox[1], self.col_height_resize_bbox[2], self.col_height_resize_bbox[3]
                    if x >= x1 and y >= y1 and x <= x2 and y <= y2:
                        self.config(cursor = "sb_v_double_arrow")
                        self.rsz_h = True
                        mouse_over_resize = True
                    else:
                        self.rsz_h = None
                except:
                    self.rsz_h = None
            if not mouse_over_resize:
                self.MT.reset_mouse_motion_creations()
        if self.extra_motion_func is not None:
            self.extra_motion_func(event)
        
    def b1_press(self, event = None):
        self.focus_set()
        self.MT.unbind("<MouseWheel>")
        x1, y1, x2, y2 = self.MT.get_canvas_visible_area()
        if self.check_mouse_position_width_resizers(event) is None:
            self.rsz_w = None
        if self.width_resizing_enabled and self.rsz_w is not None:
            self.currently_resizing_width = True
            x = self.MT.col_positions[self.rsz_w]
            line2x = self.MT.col_positions[self.rsz_w - 1]
            self.create_line(x, 0, x, self.current_height, width = 1, fill = self.resizing_line_color, tag = "rwl")
            self.MT.create_line(x, y1, x, y2, width = 1, fill = self.resizing_line_color, tag = "rwl")
            self.create_line(line2x, 0, line2x, self.current_height,width = 1, fill = self.resizing_line_color, tag = "rwl2")
            self.MT.create_line(line2x, y1, line2x, y2, width = 1, fill = self.resizing_line_color, tag = "rwl2")
        elif self.height_resizing_enabled and self.rsz_w is None and self.rsz_h is not None:
            self.currently_resizing_height = True
            y = event.y
            if y < self.MT.hdr_min_rh:
                y = int(self.MT.hdr_min_rh)
            self.new_col_height = y
            self.create_line(x1, y, x2, y, width = 1, fill = self.resizing_line_color, tag = "rhl")
        elif self.MT.identify_col(x = event.x, allow_end = False) is None:
            self.MT.deselect("all")
        elif self.col_selection_enabled and self.rsz_w is None and self.rsz_h is None:
            c = self.MT.identify_col(x = event.x)
            if c < len(self.MT.col_positions) - 1:
                self.select_col(c, redraw = True)
        if self.extra_b1_press_func is not None:
            self.extra_b1_press_func(event)
    
    def b1_motion(self, event):
        x1, y1, x2, y2 = self.MT.get_canvas_visible_area()
        if self.width_resizing_enabled and self.rsz_w is not None and self.currently_resizing_width:
            x = self.canvasx(event.x)
            size = x - self.MT.col_positions[self.rsz_w - 1]
            if not size <= self.MT.min_cw and size < self.max_cw:
                self.delete("rwl")
                self.MT.delete("rwl")
                self.create_line(x, 0, x, self.current_height, width = 1, fill = self.resizing_line_color, tag = "rwl")
                self.MT.create_line(x, y1, x, y2, width = 1, fill = self.resizing_line_color, tag = "rwl")
        elif self.height_resizing_enabled and self.rsz_h is not None and self.currently_resizing_height:
            evy = event.y
            self.delete("rhl")
            self.MT.delete("rhl")
            if evy > self.current_height:
                y = self.MT.canvasy(evy - self.current_height)
                if evy > self.max_header_height:
                    evy = int(self.max_header_height)
                    y = self.MT.canvasy(evy - self.current_height)
                self.new_col_height = evy
                self.MT.create_line(x1, y, x2, y, width = 1, fill = self.resizing_line_color, tag = "rhl")
            else:
                y = evy
                if y < self.MT.hdr_min_rh:
                    y = int(self.MT.hdr_min_rh)
                self.new_col_height = y
                self.create_line(x1, y, x2, y, width = 1, fill = self.resizing_line_color, tag = "rhl")
        elif self.drag_and_drop_enabled and self.col_selection_enabled and self.MT.selected_cols and self.rsz_h is None and self.rsz_w is None and self.dragged_col is not None:
            x = self.canvasx(event.x)
            if x > 0 and x < self.MT.col_positions[-1]:
                x = event.x
                wend = self.winfo_width() 
                if x >= wend - 0:
                    if x >= wend + 15:
                        self.MT.xview_scroll(2, "units")
                        self.xview_scroll(2, "units")
                    else:
                        self.MT.xview_scroll(1, "units")
                        self.xview_scroll(1, "units")
                    self.MT.main_table_redraw_grid_and_text(redraw_header = True)
                elif x <= 0:
                    if x >= -40:
                        self.MT.xview_scroll(-1, "units")
                        self.xview_scroll(-1, "units")
                    else:
                        self.MT.xview_scroll(-2, "units")
                        self.xview_scroll(-2, "units")
                    self.MT.main_table_redraw_grid_and_text(redraw_header = True)
                rectw = self.MT.col_positions[max(self.MT.selected_cols) + 1] - self.MT.col_positions[min(self.MT.selected_cols)]
                start = self.canvasx(event.x - int(rectw / 2))
                end = self.canvasx(event.x + int(rectw / 2))
                self.delete("dd")
                self.create_rectangle(start, 0, end, self.current_height - 1, fill = self.drag_and_drop_color, outline = self.grid_color, tag = "dd")
                self.tag_raise("dd")
                self.tag_raise("t")
                self.tag_raise("v")
        elif self.MT.drag_selection_enabled and self.col_selection_enabled and self.rsz_h is None and self.rsz_w is None:
            end_col = self.MT.identify_col(x = event.x)
            if end_col < len(self.MT.col_positions) - 1 and len(self.MT.currently_selected) == 2:
                if self.MT.currently_selected[0] == "column":
                    start_col = self.MT.currently_selected[1]
                    self.MT.selected_cols = set()
                    self.MT.selected_rows = set()
                    self.MT.selected_cells = set()
                    self.RI.selected_cells = defaultdict(int)
                    self.selected_cells = defaultdict(int)
                    if end_col >= start_col:
                        for c in range(start_col, end_col + 1):
                            self.selected_cells[c] += 1
                            self.MT.selected_cols.add(c)
                    elif end_col < start_col:
                        for c in range(end_col, start_col + 1):
                            self.selected_cells[c] += 1
                            self.MT.selected_cols.add(c)
                                
                    if self.drag_selection_binding_func is not None:
                        self.drag_selection_binding_func(("columns", sorted([start_col, end_col])))
                if event.x > self.winfo_width():
                    try:
                        self.MT.xview_scroll(1, "units")
                        self.xview_scroll(1, "units")
                    except:
                        pass
                elif event.x < 0 and self.canvasx(self.winfo_width()) > 0:
                    try:
                        self.xview_scroll(-1, "units")
                        self.MT.xview_scroll(-1, "units")
                    except:
                        pass
            self.MT.main_table_redraw_grid_and_text(redraw_header = True, redraw_row_index = False)
        if self.extra_b1_motion_func is not None:
            self.extra_b1_motion_func(event)
            
    def b1_release(self, event = None):
        self.MT.bind("<MouseWheel>", self.MT.mousewheel)
        if self.width_resizing_enabled and self.rsz_w is not None and self.currently_resizing_width:
            self.currently_resizing_width = False
            new_col_pos = self.coords("rwl")[0]
            self.delete("rwl", "rwl2")
            self.MT.delete("rwl", "rwl2")
            size = new_col_pos - self.MT.col_positions[self.rsz_w - 1]
            if size < self.MT.min_cw:
                new_row_pos = ceil(self.MT.col_positions[self.rsz_w - 1] + self.MT.min_cw)
            elif size > self.max_cw:
                new_col_pos = floor(self.MT.col_positions[self.rsz_w - 1] + self.max_cw)
            increment = new_col_pos - self.MT.col_positions[self.rsz_w]
            self.MT.col_positions[self.rsz_w + 1:] = [e + increment for e in islice(self.MT.col_positions, self.rsz_w + 1, len(self.MT.col_positions))]
            self.MT.col_positions[self.rsz_w] = new_col_pos
            self.MT.main_table_redraw_grid_and_text(redraw_header = True, redraw_row_index = True)
        elif self.height_resizing_enabled and self.rsz_h is not None and self.currently_resizing_height:
            self.currently_resizing_height = False
            self.delete("rhl")
            self.MT.delete("rhl")
            self.set_height(self.new_col_height,set_TL = True)
            self.MT.main_table_redraw_grid_and_text(redraw_header = True, redraw_row_index = True)
        if self.drag_and_drop_enabled and self.col_selection_enabled and self.MT.selected_cols and self.rsz_h is None and self.rsz_w is None and self.dragged_col is not None:
            self.delete("dd")
            x = event.x
            c = self.MT.identify_col(x = x)
            if c != self.dragged_col and c is not None and c not in self.MT.selected_cols and len(self.MT.selected_cols) != (len(self.MT.col_positions) - 1):
                colsiter = list(self.MT.selected_cols)
                colsiter.sort()
                stins = colsiter[0]
                endins = colsiter[-1] + 1
                if self.dragged_col < c and c >= len(self.MT.col_positions) - 1:
                    c -= 1
                c_ = int(c)
                if c >= endins:
                    c += 1
                if self.ch_extra_drag_drop_func is not None:
                    self.ch_extra_drag_drop_func(self.MT.selected_cols, int(c_))
                else:
                    if self.MT.all_columns_displayed:
                        if stins > c:
                            for rn in range(len(self.MT.data_ref)):
                                self.MT.data_ref[rn][c:c] = self.MT.data_ref[rn][stins:endins]
                                self.MT.data_ref[rn][stins + len(colsiter):endins + len(colsiter)] = []
                            if not isinstance(self.MT.my_hdrs, int) and self.MT.my_hdrs:
                                try:
                                    self.MT.my_hdrs[c:c] = self.MT.my_hdrs[stins:endins]
                                    self.MT.my_hdrs[stins + len(colsiter):endins + len(colsiter)] = []
                                except:
                                    pass
                        else:
                            for rn in range(len(self.MT.data_ref)):
                                self.MT.data_ref[rn][c:c] = self.MT.data_ref[rn][stins:endins]
                                self.MT.data_ref[rn][stins:endins] = []
                            if not isinstance(self.MT.my_hdrs, int) and self.MT.my_hdrs:
                                try:
                                    self.MT.my_hdrs[c:c] = self.MT.my_hdrs[stins:endins]
                                    self.MT.my_hdrs[stins:endins] = []
                                except:
                                    pass
                    else:
                        c_ = int(c)
                        if c >= endins:
                            c += 1
                        if stins > c:
                            self.MT.displayed_columns[c:c] = self.MT.displayed_columns[stins:endins]
                            self.MT.displayed_columns[stins + len(colsiter):endins + len(colsiter)] = []
                            if not isinstance(self.MT.my_hdrs, int) and self.MT.my_hdrs:
                                try:
                                    self.MT.my_hdrs[c:c] = self.MT.my_hdrs[stins:endins]
                                    self.MT.my_hdrs[stins + len(colsiter):endins + len(colsiter)] = []
                                except:
                                    pass
                        else:
                            self.MT.displayed_columns[c:c] = self.MT.displayed_columns[stins:endins]
                            self.MT.displayed_columns[stins + len(colsiter):endins + len(colsiter)] = []
                            if not isinstance(self.MT.my_hdrs, int) and self.MT.my_hdrs:
                                try:
                                    self.MT.my_hdrs[c:c] = self.MT.my_hdrs[stins:endins]
                                    self.MT.my_hdrs[stins:endins] = []
                                except:
                                    pass
                cws = self.MT.parentframe.get_column_widths()
                if stins > c:
                    cws[c:c] = cws[stins:endins]
                    cws[stins + len(colsiter):endins + len(colsiter)] = []
                else:
                    cws[c:c] = cws[stins:endins]
                    cws[stins:endins] = []
                self.MT.parentframe.set_column_widths(cws)
                if (c_ - 1) + len(colsiter) > len(self.MT.col_positions) - 1:
                    sels_start = len(self.MT.col_positions) - 1 - len(colsiter)
                    newcolidxs = tuple(range(sels_start, len(self.MT.col_positions) - 1))
                else:
                    if c_ > endins:
                        c_ += 1
                        sels_start = c_ - len(colsiter)
                    else:
                        if c_ == endins and len(colsiter) == 1:
                            pass
                        else:
                            if c_ > endins:
                                c_ += 1
                            if c_ == endins:
                                c_ -= 1
                            if c_ < 0:
                                c_ = 0
                        sels_start = c_
                    newcolidxs = tuple(range(sels_start, sels_start + len(colsiter)))
                self.MT.selected_rows = set()
                self.MT.selected_cells = set()
                self.selected_cells = defaultdict(int)
                self.RI.selected_cells = defaultdict(int)
                self.MT.selected_cols = set()
                for colsel in newcolidxs:
                    self.MT.selected_cols.add(colsel)
                    self.selected_cells[colsel] += 1
                self.MT.undo_storage = deque(maxlen = 20)
                self.MT.main_table_redraw_grid_and_text(redraw_header = True, redraw_row_index = True)
        self.dragged_col = None
        self.currently_resizing_width = False
        self.currently_resizing_height = False
        self.rsz_w = None
        self.rsz_h = None
        self.mouse_motion(event)
        if self.extra_b1_release_func is not None:
            self.extra_b1_release_func(event)

    def double_b1(self, event = None):
        self.focus_set()
        if self.double_click_resizing_enabled and self.width_resizing_enabled and self.rsz_w is not None and not self.currently_resizing_width:
            # condition check if trying to resize width:
            col = self.rsz_w - 1
            self.set_col_width(col)
            self.MT.main_table_redraw_grid_and_text(redraw_header = True, redraw_row_index = True)
            self.mouse_motion(event)
        self.rsz_w = None
        if self.extra_double_b1_func is not None:
            self.extra_double_b1_func(event)

    def select_col(self, c, redraw = False):
        c = int(c)
        self.selected_cells = defaultdict(int)
        self.selected_cells[c] += 1
        self.RI.selected_cells = defaultdict(int)
        self.MT.selected_cols = {c}
        self.MT.selected_rows = set()
        self.MT.selected_cells = set()
        self.MT.currently_selected = ("column", c)
        if redraw:
            self.MT.main_table_redraw_grid_and_text(redraw_header = True, redraw_row_index = True)
        if self.selection_binding_func is not None:
            self.selection_binding_func(("column", c))

    def highlight_cells(self, c = 0, cells = tuple(), bg = None, fg = None, redraw = False):
        if bg is None and fg is None:
            return
        if cells:
            self.highlighted_cells = {c_: (bg, fg)  for c_ in cells}
        else:
            self.highlighted_cells[c] = (bg, fg)
        if redraw:
            self.MT.main_table_redraw_grid_and_text(True, False)

    def add_selection(self, c, redraw = False, run_binding_func = True):
        c = int(c)
        self.MT.currently_selected = ("column", c)
        self.selected_cells[c] += 1
        self.MT.selected_cols.add(c)
        if redraw:
            self.MT.main_table_redraw_grid_and_text(redraw_header = True, redraw_row_index = True)
        if self.selection_binding_func is not None and run_binding_func:
            self.selection_binding_func(("column", c))

    def set_col_width(self, col, width = None, only_set_if_too_small = False):
        if col < 0:
            return
        if width is None:
            if self.MT.all_columns_displayed:
                try:
                    hw = self.MT.GetHdrTextWidth(self.GetLargestWidth(self.MT.my_hdrs[col])) + 10
                except:
                    hw = self.MT.GetHdrTextWidth(str(col)) + 10
                x1, y1, x2, y2 = self.MT.get_canvas_visible_area()
                start_row, end_row = self.MT.get_visible_rows(y1, y2)
                dtw = 0
                for r in islice(self.MT.data_ref, start_row, end_row):
                    try:
                        w = self.MT.GetTextWidth(self.GetLargestWidth(r[col]))
                        if w > dtw:
                            dtw = w
                    except:
                        pass
            else:
                try:
                    hw = self.MT.GetHdrTextWidth(self.GetLargestWidth(self.MT.my_hdrs[self.MT.displayed_columns[col]])) + 10 
                except:
                    hw = self.MT.GetHdrTextWidth(str(col)) + 10
                x1, y1, x2, y2 = self.MT.get_canvas_visible_area()
                start_row,end_row = self.MT.get_visible_rows(y1, y2)
                dtw = 0
                for r in islice(self.MT.data_ref, start_row,end_row):
                    try:
                        w = self.MT.GetTextWidth(self.GetLargestWidth(r[self.MT.displayed_columns[col]]))
                        if w > dtw:
                            dtw = w
                    except:
                        pass 
            dtw += 10
            if dtw > hw:
                width = dtw
            else:
                width = hw
        if width <= self.MT.min_cw:
            width = int(self.MT.min_cw)
        elif width > self.max_cw:
            width = int(self.max_cw)
        if only_set_if_too_small:
            if width <= self.MT.col_positions[col + 1] - self.MT.col_positions[col]:
                return
        new_col_pos = self.MT.col_positions[col] + width
        increment = new_col_pos - self.MT.col_positions[col + 1]
        self.MT.col_positions[col + 2:] = [e + increment for e in islice(self.MT.col_positions, col + 2, len(self.MT.col_positions))]
        self.MT.col_positions[col + 1] = new_col_pos

    def GetLargestWidth(self, cell):
        return max(cell.split("\n"), key = self.MT.GetTextWidth)

    def redraw_grid_and_text(self, last_col_line_pos, x1, x_stop, start_col, end_col):
        try:
            self.configure(scrollregion = (0, 0, last_col_line_pos + 150, self.current_height))
            self.delete("h", "v", "t", "s", "fv")
            self.visible_col_dividers = []
            x = self.MT.col_positions[start_col]
            self.create_line(x, 0, x, self.current_height, fill = self.grid_color, width = 1, tag = "fv")
            self.col_height_resize_bbox = (x1, self.current_height - 4, x_stop, self.current_height)
            yend = self.current_height - 5
            if self.width_resizing_enabled:
                for c in range(start_col + 1, end_col):
                    x = self.MT.col_positions[c]
                    self.visible_col_dividers.append((x - 4, 1, x + 4, yend))
                    self.create_line(x, 0, x, self.current_height, fill = self.grid_color, width = 1, tag = ("v", f"{c}"))
            else:
                for c in range(start_col + 1, end_col):
                    x = self.MT.col_positions[c]
                    self.create_line(x, 0, x, self.current_height, fill = self.grid_color, width = 1, tag = ("v", f"{c}"))
            top = self.canvasy(0)
            if self.MT.hdr_fl_ins + self.MT.hdr_half_txt_h > top:
                incfl = True
            else:
                incfl = False
            c_2 = self.selected_cells_background if self.selected_cells_background.startswith("#") else Color_Map_[self.selected_cells_background]
            if self.MT.all_columns_displayed:
                if self.align == "center":
                    for c in range(start_col, end_col - 1):
                        fc = self.MT.col_positions[c]
                        sc = self.MT.col_positions[c + 1]
                        if c in self.highlighted_cells and (c in self.selected_cells or c in self.MT.selected_cols):
                            c_1 = self.highlighted_cells[c][0] if self.highlighted_cells[c][0].startswith("#") else Color_Map_[self.highlighted_cells[c][0]]
                            self.create_rectangle(fc + 1,
                                                  0,
                                                  sc,
                                                  self.current_height - 1,
                                                  fill = (f"#{int((int(c_1[1:3], 16) + int(c_2[1:3], 16)) / 2):02X}" +
                                                          f"{int((int(c_1[3:5], 16) + int(c_2[3:5], 16)) / 2):02X}" +
                                                          f"{int((int(c_1[5:], 16) + int(c_2[5:], 16)) / 2):02X}"),
                                                  outline = "",
                                                  tag = "s")
                            tf = self.selected_cells_foreground if self.highlighted_cells[c][1] is None else self.highlighted_cells[c][1]
                        elif c in (self.MT.selected_cols or self.selected_cells):
                            self.create_rectangle(fc + 1, 0, sc, self.current_height - 1, fill = self.selected_cells_background, outline = "", tag = "s")
                            tf = self.selected_cells_foreground
                        elif c in self.highlighted_cells:
                            self.create_rectangle(fc + 1, 0, sc, self.current_height - 1, fill = self.highlighted_cells[c][0], outline = "", tag = "s")
                            tf = self.text_color if self.highlighted_cells[c][1] is None else self.highlighted_cells[c][1]
                        else:
                            tf = self.text_color
                        if fc + 7 > x_stop:
                            continue
                        mw = sc - fc - 5
                        x = fc + floor(mw / 2)
                        if isinstance(self.MT.my_hdrs, int):
                            try:
                                lns = self.MT.data_ref[self.MT.my_hdrs][c].split("\n")
                            except:
                                lns = (f"{c + 1}", )
                        else:
                            try:
                                lns = self.MT.my_hdrs[c].split("\n")
                            except:
                                lns = (f"{c + 1}", )
                        y = self.MT.hdr_fl_ins
                        if incfl:
                            fl = lns[0]
                            t = self.create_text(x, y, text = fl, fill = tf, font = self.MT.my_hdr_font, anchor = "center", tag = "t")
                            wd = self.bbox(t)
                            wd = wd[2] - wd[0]
                            if wd > mw:
                                tl = len(fl)
                                slce = tl - floor(tl * (mw / wd))
                                if slce % 2:
                                    slce += 1
                                else:
                                    slce += 2
                                slce = int(slce / 2)
                                fl = fl[slce:tl - slce]
                                self.itemconfig(t, text = fl)
                                wd = self.bbox(t)
                                while wd[2] - wd[0] > mw:
                                    fl = fl[1: - 1]
                                    self.itemconfig(t, text = fl)
                                    wd = self.bbox(t)
                        if len(lns) > 1:
                            stl = int((top - y) / self.MT.hdr_xtra_lines_increment) - 1
                            if stl < 1:
                                stl = 1
                            y += (stl * self.MT.hdr_xtra_lines_increment)
                            if y + self.MT.hdr_half_txt_h < self.current_height:
                                for i in range(stl, len(lns)):
                                    txt = lns[i]
                                    t = self.create_text(x, y, text = txt, fill = tf, font = self.MT.my_hdr_font, anchor = "center", tag = "t")
                                    wd = self.bbox(t)
                                    wd = wd[2] - wd[0]
                                    if wd > mw:
                                        tl = len(txt)
                                        slce = tl - floor(tl * (mw / wd))
                                        if slce % 2:
                                            slce += 1
                                        else:
                                            slce += 2
                                        slce = int(slce / 2)
                                        txt = txt[slce:tl - slce]
                                        self.itemconfig(t, text = txt)
                                        wd = self.bbox(t)
                                        while wd[2] - wd[0] > mw:
                                            txt = txt[1: - 1]
                                            self.itemconfig(t, text = txt)
                                            wd = self.bbox(t)
                                    y += self.MT.hdr_xtra_lines_increment
                                    if y + self.MT.hdr_half_txt_h > self.current_height:
                                        break
                elif self.align == "w":
                    for c in range(start_col, end_col - 1):
                        fc = self.MT.col_positions[c]
                        sc = self.MT.col_positions[c + 1]
                        if c in self.highlighted_cells and (c in self.selected_cells or c in self.MT.selected_cols):
                            c_1 = self.highlighted_cells[c][0] if self.highlighted_cells[c][0].startswith("#") else Color_Map_[self.highlighted_cells[c][0]]
                            self.create_rectangle(fc + 1,
                                                  0,
                                                  sc,
                                                  self.current_height - 1,
                                                  fill = (f"#{int((int(c_1[1:3], 16) + int(c_2[1:3], 16)) / 2):02X}" +
                                                          f"{int((int(c_1[3:5], 16) + int(c_2[3:5], 16)) / 2):02X}" +
                                                          f"{int((int(c_1[5:], 16) + int(c_2[5:], 16)) / 2):02X}"),
                                                  outline = "",
                                                  tag = "s")
                            tf = self.selected_cells_foreground if self.highlighted_cells[c][1] is None else self.highlighted_cells[c][1]
                        elif c in (self.MT.selected_cols or self.selected_cells):
                            self.create_rectangle(fc + 1, 0, sc, self.current_height - 1, fill = self.selected_cells_background, outline = "", tag = "s")
                            tf = self.selected_cells_foreground
                        elif c in self.highlighted_cells:
                            self.create_rectangle(fc + 1, 0, sc, self.current_height - 1, fill = self.highlighted_cells[c][0], outline = "", tag = "s")
                            tf = self.text_color if self.highlighted_cells[c][1] is None else self.highlighted_cells[c][1]
                        else:
                            tf = self.text_color
                        mw = sc - fc - 5
                        x = fc + 7
                        if x > x_stop:
                            continue
                        if isinstance(self.MT.my_hdrs, int):
                            try:
                                lns = self.MT.data_ref[self.MT.my_hdrs][c].split("\n")
                            except:
                                lns = (f"{c + 1}", )
                        else:
                            try:
                                lns = self.MT.my_hdrs[c].split("\n")
                            except:
                                lns = (f"{c + 1}", )
                        y = self.MT.hdr_fl_ins
                        if incfl:
                            fl = lns[0]
                            t = self.create_text(x, y, text = fl, fill = tf, font = self.MT.my_hdr_font, anchor = "w", tag = "t")
                            wd = self.bbox(t)
                            wd = wd[2] - wd[0]
                            if wd > mw:
                                nl = int(len(fl) * (mw / wd)) - 1
                                self.itemconfig(t, text = fl[:nl])
                                wd = self.bbox(t)
                                while wd[2] - wd[0] > mw:
                                    nl -= 1
                                    self.dchars(t, nl)
                                    wd = self.bbox(t)
                        if len(lns) > 1:
                            stl = int((top - y) / self.MT.hdr_xtra_lines_increment) - 1
                            if stl < 1:
                                stl = 1
                            y += (stl * self.MT.hdr_xtra_lines_increment)
                            if y + self.MT.hdr_half_txt_h < self.current_height:
                                for i in range(stl, len(lns)):
                                    txt = lns[i]
                                    t = self.create_text(x, y, text = txt, fill = tf, font = self.MT.my_hdr_font, anchor = "w", tag = "t")
                                    wd = self.bbox(t)
                                    wd = wd[2] - wd[0]
                                    if wd > mw:
                                        nl = int(len(txt) * (mw / wd)) - 1
                                        self.itemconfig(t, text = txt[:nl])
                                        wd = self.bbox(t)
                                        while wd[2] - wd[0] > mw:
                                            nl -= 1
                                            self.dchars(t, nl)
                                            wd = self.bbox(t)
                                    y += self.MT.hdr_xtra_lines_increment
                                    if y + self.MT.hdr_half_txt_h > self.current_height:
                                        break
            else:
                if self.align == "center":
                    for c in range(start_col, end_col - 1):
                        fc = self.MT.col_positions[c]
                        sc = self.MT.col_positions[c + 1]
                        if self.MT.displayed_columns[c] in self.highlighted_cells and (c in self.selected_cells or c in self.MT.selected_cols):
                            c_1 = self.highlighted_cells[self.MT.displayed_columns[c]][0] if self.highlighted_cells[self.MT.displayed_columns[c]][0].startswith("#") else Color_Map_[self.highlighted_cells[self.MT.displayed_columns[c]][0]]
                            self.create_rectangle(fc + 1,
                                                  0,
                                                  sc,
                                                  self.current_height - 1,
                                                  fill = (f"#{int((int(c_1[1:3], 16) + int(c_2[1:3], 16)) / 2):02X}" +
                                                          f"{int((int(c_1[3:5], 16) + int(c_2[3:5], 16)) / 2):02X}" +
                                                          f"{int((int(c_1[5:], 16) + int(c_2[5:], 16)) / 2):02X}"),
                                                  outline = "",
                                                  tag = "s")
                            tf = self.selected_cells_foreground if self.highlighted_cells[c][1] is None else self.highlighted_cells[c][1]
                        elif c in (self.MT.selected_cols or self.selected_cells):
                            self.create_rectangle(fc + 1, 0, sc, self.current_height - 1, fill = self.selected_cells_background, outline = "", tag = "s")
                            tf = self.selected_cells_foreground
                        elif self.MT.displayed_columns[c] in self.highlighted_cells:
                            self.create_rectangle(fc + 1, 0, sc, self.current_height - 1, fill = self.highlighted_cells[self.MT.displayed_columns[c]][0], outline = "", tag = "s")
                            tf = self.text_color if self.highlighted_cells[self.MT.displayed_columns[c]][1] is None else self.highlighted_cells[self.MT.displayed_columns[c]][1]
                        else:
                            tf = self.text_color
                        if fc + 7 > x_stop:
                            continue
                        mw = sc - fc - 5
                        x = fc + floor(mw / 2)
                        if isinstance(self.MT.my_hdrs, int):
                            try:
                                lns = self.MT.data_ref[self.MT.my_hdrs][c].split("\n")
                            except:
                                lns = (f"{c + 1}", )
                        else:
                            try:
                                lns = self.MT.my_hdrs[self.MT.displayed_columns[c]].split("\n")
                            except:
                                lns = (f"{c + 1}", )
                        y = self.MT.hdr_fl_ins
                        if incfl:
                            fl = lns[0]
                            t = self.create_text(x, y, text = fl, fill = tf, font = self.MT.my_hdr_font, anchor = "center", tag = "t")
                            wd = self.bbox(t)
                            wd = wd[2] - wd[0]
                            if wd > mw:
                                tl = len(fl)
                                slce = tl - floor(tl * (mw / wd))
                                if slce % 2:
                                    slce += 1
                                else:
                                    slce += 2
                                slce = int(slce / 2)
                                fl = fl[slce:tl - slce]
                                self.itemconfig(t, text = fl)
                                wd = self.bbox(t)
                                while wd[2] - wd[0] > mw:
                                    fl = fl[1: - 1]
                                    self.itemconfig(t, text = fl)
                                    wd = self.bbox(t)
                        if len(lns) > 1:
                            stl = int((top - y) / self.MT.hdr_xtra_lines_increment) - 1
                            if stl < 1:
                                stl = 1
                            y += (stl * self.MT.hdr_xtra_lines_increment)
                            if y + self.MT.hdr_half_txt_h < self.current_height:
                                for i in range(stl, len(lns)):
                                    txt = lns[i]
                                    t = self.create_text(x, y, text = txt, fill = tf, font = self.MT.my_hdr_font, anchor = "center", tag = "t")
                                    wd = self.bbox(t)
                                    wd = wd[2] - wd[0]
                                    if wd > mw:
                                        tl = len(txt)
                                        slce = tl - floor(tl * (mw / wd))
                                        if slce % 2:
                                            slce += 1
                                        else:
                                            slce += 2
                                        slce = int(slce / 2)
                                        txt = txt[slce:tl - slce]
                                        self.itemconfig(t, text = txt)
                                        wd = self.bbox(t)
                                        while wd[2] - wd[0] > mw:
                                            txt = txt[1: - 1]
                                            self.itemconfig(t, text = txt)
                                            wd = self.bbox(t)
                                    y += self.MT.hdr_xtra_lines_increment
                                    if y + self.MT.hdr_half_txt_h > self.current_height:
                                        break
                elif self.align == "w":
                    for c in range(start_col, end_col - 1):
                        fc = self.MT.col_positions[c]
                        sc = self.MT.col_positions[c + 1]
                        if self.MT.displayed_columns[c] in self.highlighted_cells and (c in self.selected_cells or c in self.MT.selected_cols):
                            c_1 = self.highlighted_cells[self.MT.displayed_columns[c]][0] if self.highlighted_cells[self.MT.displayed_columns[c]][0].startswith("#") else Color_Map_[self.highlighted_cells[self.MT.displayed_columns[c]][0]]
                            self.create_rectangle(fc + 1,
                                                  0,
                                                  sc,
                                                  self.current_height - 1,
                                                  fill = (f"#{int((int(c_1[1:3], 16) + int(c_2[1:3], 16)) / 2):02X}" +
                                                          f"{int((int(c_1[3:5], 16) + int(c_2[3:5], 16)) / 2):02X}" +
                                                          f"{int((int(c_1[5:], 16) + int(c_2[5:], 16)) / 2):02X}"),
                                                  outline = "",
                                                  tag = "s")
                            tf = self.selected_cells_foreground if self.highlighted_cells[c][1] is None else self.highlighted_cells[c][1]
                        elif c in (self.MT.selected_cols or self.selected_cells):
                            self.create_rectangle(fc + 1, 0, sc, self.current_height - 1, fill = self.selected_cells_background, outline = "", tag = "s")
                            tf = self.selected_cells_foreground
                        elif self.MT.displayed_columns[c] in self.highlighted_cells:
                            self.create_rectangle(fc + 1, 0, sc, self.current_height - 1, fill = self.highlighted_cells[self.MT.displayed_columns[c]][0], outline = "", tag = "s")
                            tf = self.text_color if self.highlighted_cells[self.MT.displayed_columns[c]][1] is None else self.highlighted_cells[self.MT.displayed_columns[c]][1]
                        else:
                            tf = self.text_color
                        mw = sc - fc - 5
                        x = fc + 7
                        if x > x_stop:
                            continue
                        if isinstance(self.MT.my_hdrs, int):
                            try:
                                lns = self.MT.data_ref[self.MT.my_hdrs][c].split("\n")
                            except:
                                lns = (f"{c + 1}", )
                        else:
                            try:
                                lns = self.MT.my_hdrs[self.MT.displayed_columns[c]].split("\n")
                            except:
                                lns = (f"{c + 1}", )
                        y = self.MT.hdr_fl_ins
                        if incfl:
                            fl = lns[0]
                            t = self.create_text(x, y, text = fl, fill = tf, font = self.MT.my_hdr_font, anchor = "w", tag = "t")
                            wd = self.bbox(t)
                            wd = wd[2] - wd[0]
                            if wd > mw:
                                nl = int(len(fl) * (mw / wd)) - 1
                                self.itemconfig(t, text = fl[:nl])
                                wd = self.bbox(t)
                                while wd[2] - wd[0] > mw:
                                    nl -= 1
                                    self.dchars(t, nl)
                                    wd = self.bbox(t)
                        if len(lns) > 1:
                            stl = int((top - y) / self.MT.hdr_xtra_lines_increment) - 1
                            if stl < 1:
                                stl = 1
                            y += (stl * self.MT.hdr_xtra_lines_increment)
                            if y + self.MT.hdr_half_txt_h < self.current_height:
                                for i in range(stl, len(lns)):
                                    txt = lns[i]
                                    t = self.create_text(x, y, text = txt, fill = tf, font = self.MT.my_hdr_font, anchor = "w", tag = "t")
                                    wd = self.bbox(t)
                                    wd = wd[2] - wd[0]
                                    if wd > mw:
                                        nl = int(len(txt) * (mw / wd)) - 1
                                        self.itemconfig(t, text = txt[:nl])
                                        wd = self.bbox(t)
                                        while wd[2] - wd[0] > mw:
                                            nl -= 1
                                            self.dchars(t, nl)
                                            wd = self.bbox(t)
                                    y += self.MT.hdr_xtra_lines_increment
                                    if y + self.MT.hdr_half_txt_h > self.current_height:
                                        break
            self.create_line(x1, self.current_height - 1, x_stop, self.current_height - 1, fill = self.header_border_color, width = 1, tag = "h")
        except:
            return
        
    def GetCellCoords(self, event = None, r = None, c = None):
        pass

    