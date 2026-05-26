import tkinter as tk
from tkinter import ttk, messagebox
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
from matplotlib.figure import Figure
import matplotlib.animation as animation
from matplotlib.patches import Circle, Rectangle, Polygon
from matplotlib.ticker import FuncFormatter
import matplotlib as mpl
import os
from tkinter import filedialog
import json
import pygame
import wave
import contextlib
from moviepy import VideoFileClip, AudioFileClip, ImageSequenceClip
import tempfile
import shutil
import time
import traceback
import concurrent.futures
from queue import Queue

# 配置moviepy使用imageio_ffmpeg（对打包后的exe很重要）
try:
    from imageio_ffmpeg import get_ffmpeg_exe
    os.environ['IMAGEIO_FFMPEG_EXE'] = get_ffmpeg_exe()
except:
    pass  # 如果失败，moviepy会尝试使用系统ffmpeg

class AnimationLoop:
    def __init__(self, app):
        self.app = app
        self.running = False
        self.after_id = None
        self.animation_start_time = None  # 动画开始的绝对时间
        self.animation_start_second = 0  # 动画开始时的current_second
        self.frame_count = 0
        self.fps_start_time = None
        self.target_fps = 15  # 目标刷新率（平衡流畅度和音频质量）
        self.update_interval = 1000 // self.target_fps  # 更新间隔
        self.audio_started = False  # 添加标志位，用于跟踪音频是否已开始播放
        self.audio_start_time = None  # 音频开始播放的时间戳

    def start(self):
        if not self.running:
            print("🎬 动画循环开始")
            self.running = True
            # 记录动画开始的绝对时间和起始秒数
            self.animation_start_time = self.app.root.tk.call('clock', 'milliseconds')
            self.animation_start_second = self.app.current_second
            self.fps_start_time = self.animation_start_time
            self.frame_count = 0
            self.audio_started = False  # 重置音频播放状态
            self.audio_start_time = None  # 重置音频开始时间
            print(f"   起始时间: {self.animation_start_second:.2f}秒")
            self._update()

    def stop(self):
        if self.running:
            print("⏸️ 动画循环停止")
            self.running = False
            if self.after_id:
                self.app.root.after_cancel(self.after_id)
                self.after_id = None
            # 暂停音频播放
            if self.app.audio_file:
                pygame.mixer.music.pause()
            self.audio_started = False  # 重置音频播放状态
            self.audio_start_time = None

    def _update(self):
        if not self.running:
            return

        # 如果用户正在拖动时间轴，暂停动画时间更新，但保持循环运行
        if self.app.is_user_dragging_timeline:
            # 用户正在拖动，重置动画起始时间以避免时间跳跃
            self.animation_start_time = self.app.root.tk.call('clock', 'milliseconds')
            self.animation_start_second = self.app.current_second
            if hasattr(self, 'last_sync_check'):
                self.last_sync_check = self.animation_start_time
            # 继续循环，但不更新时间
            if self.running:
                self.after_id = self.app.root.after(self.update_interval, self._update)
            return

        # 获取当前真实时间
        current_time = self.app.root.tk.call('clock', 'milliseconds')
        
        # 计算从动画开始经过的真实时间（秒）
        elapsed_real_time = (current_time - self.animation_start_time) / 1000.0
        
        # 根据播放速度计算当前应该在的动画时间
        target_second = self.animation_start_second + (elapsed_real_time * self.app.playback_speed)
        
        # 检查是否到达终点
        if target_second >= self.app.total_seconds:
            target_second = self.app.total_seconds - 0.01
            self.app.current_second = target_second
            self.app.current_frame = int(self.app.current_second * self.app.fps)
            self.app.current_frame = max(0, min(self.app.current_frame, self.app.total_frames - 1))
            
            # 更新UI
            self._update_ui()
            
            # 停止播放
            self.stop()
            self.app.is_playing = False
            self.app.fixed_view_range = None
            print("✅ 动画播放完成")
            return
        
        # 更新当前时间
        self.app.current_second = target_second
        self.app.current_frame = int(self.app.current_second * self.app.fps)
        self.app.current_frame = max(0, min(self.app.current_frame, self.app.total_frames - 1))
        if len(self.app.text_box["contents"]) > 0:
            self.app.current_frame = min(self.app.current_frame, len(self.app.text_box["contents"]) - 1)
        
        # 音频同步处理 - 优化版，减少但不完全禁用自动同步
        if self.app.audio_file:
            if not self.audio_started:
                # 首次启动音频
                # pygame.mixer.music.play(loops, start, fade_ms)
                # loops=0表示播放一次，start是开始位置（秒）
                pygame.mixer.music.play(loops=0, start=self.app.current_second)
                self.audio_started = True
                self.audio_start_time = current_time
                print(f"🎵 音频开始播放，起始位置: {self.app.current_second:.2f}秒")
                # 初始化同步检查时间
                self.last_sync_check = current_time
            elif hasattr(self, 'last_sync_check') and (current_time - self.last_sync_check > 10000):
                # 每10秒检查一次音频同步（较低频率以减少杂音）
                audio_elapsed = (current_time - self.audio_start_time) / 1000.0 * self.app.playback_speed
                expected_position = self.animation_start_second + audio_elapsed
                position_diff = abs(self.app.current_second - expected_position)
                
                # 只有偏差超过0.5秒才重新同步（较大容差以减少同步频率）
                if position_diff > 0.5:
                    # 使用平滑的重新同步方式，减少杂音
                    current_volume = pygame.mixer.music.get_volume()
                    pygame.mixer.music.set_volume(0.0)
                    pygame.mixer.music.stop()
                    pygame.mixer.music.set_volume(current_volume)
                    pygame.mixer.music.play(loops=0, start=self.app.current_second)
                    self.audio_start_time = current_time
                    print(f"🔄 音频重新同步到 {self.app.current_second:.2f}秒 (偏差: {position_diff:.2f}s)")
                self.last_sync_check = current_time
            elif not hasattr(self, 'last_sync_check'):
                self.last_sync_check = current_time
        
        # 更新UI
        self._update_ui()
        
        # FPS统计
        self.frame_count += 1
        if current_time - self.fps_start_time >= 1000:
            actual_fps = self.frame_count
            self.frame_count = 0
            self.fps_start_time = current_time
            # 显示时间偏差（用于调试）
            time_diff = self.app.current_second - target_second
            print(f"📊 刷新率: {actual_fps} FPS | 当前时间: {self.app.current_second:.2f}s | 偏差: {abs(time_diff)*1000:.1f}ms")
        
        # 计算下一次更新的延迟，动态调整以保持同步
        next_delay = self.update_interval
        
        # 安排下一帧
        if self.running:
            self.after_id = self.app.root.after(next_delay, self._update)
    
    def _update_ui(self):
        """更新UI显示"""
        # 更新时间轴滑块（如果用户没有在拖动的话）
        if not self.app.is_user_dragging_timeline:
            self.app.is_time_scale_updating = True
            self.app.time_scale.set(self.app.current_second)
            self.app.is_time_scale_updating = False
        
        # 更新文本框内容
        self.app.text_content_entry.delete(0, tk.END)
        if (self.app.current_frame < len(self.app.text_box["contents"]) and 
            self.app.current_frame >= 0):
            self.app.text_content_entry.insert(0, self.app.text_box["contents"][self.app.current_frame])
        
        # 更新时间显示
        self.app.text_second_entry.delete(0, tk.END)
        self.app.text_second_entry.insert(0, str(int(self.app.current_second)))
        
        # 清理临时关键帧
        self.app.cleanup_temp_keyframes_on_time_change()
        
        # 更新舞台预览
        self.app.update_stage_preview()

class StageAnimationTool:
    def __init__(self, root):
        # 初始化pygame音频 - 使用适当的参数避免杂音
        # frequency: 44100Hz (标准音频采样率)
        # size: -16 (16位音频)
        # channels: 2 (立体声)
        # buffer: 16384 (超大缓冲区，彻底避免音频欠载导致的杂音)
        # allowedchanges: 0 (不允许改变音频格式，确保一致性)
        pygame.mixer.quit()  # 先退出以确保干净初始化
        pygame.mixer.init(frequency=44100, size=-16, channels=2, buffer=16384, allowedchanges=0)
        pygame.mixer.music.set_volume(1.0)  # 先设置为最大音量，后续再调整
        
        # 设置matplotlib中文字体
        plt.rcParams['font.sans-serif'] = ['SimHei']  # 用来正常显示中文标签
        plt.rcParams['axes.unicode_minus'] = False  # 用来正常显示负号
        
        self.root = root
        self.root.title("舞台走位动画制作工具 v2.3")
        
        # 设置窗口最小尺寸，避免内容变化导致窗口跳动
        self.root.minsize(1400, 800)
        
        # 设置窗口初始大小（不指定位置，让系统自动决定）
        # 不使用 geometry() 设置位置，避免后续操作导致窗口跳动
        # self.root.geometry("1400x900")
        
        # 让窗口在屏幕上居中显示
        window_width = 1400
        window_height = 900
        screen_width = self.root.winfo_screenwidth()
        screen_height = self.root.winfo_screenheight()
        x = (screen_width - window_width) // 2
        y = (screen_height - window_height) // 2
        # 只在首次启动时设置位置，之后不再修改
        self.root.geometry(f"{window_width}x{window_height}+{x}+{y}")
        
        # 添加标志，表示窗口已经初始化完成
        self.window_initialized = False  # 将在 UI 创建完成后设置为 True
        
        # 音频相关属性
        self.audio_file = None
        self.audio_duration = 0
        self.audio_volume = 0.5  # 默认音量为50%
        pygame.mixer.music.set_volume(self.audio_volume)  # 设置初始音量
        
        # 舞台参数
        self.stage_width = 20
        self.stage_height = 15
        
        # 动画控制
        self.fps = 60  # 每秒帧数
        self.total_seconds = 10  # 初始总秒数
        self.total_frames = int(self.total_seconds * self.fps)  # 总帧数
        self.current_frame = 0
        self.current_second = 0
        self.playback_speed = 1.0  # 添加播放速度属性
        self.speed_options = [0.25, 0.5, 0.75, 1.0, 1.5, 2.0, 3.0, 4.0]  # 预设速度选项
        
        # 存储文本框信息
        self.text_box = {
            "contents": ["" for _ in range(self.total_frames)],  # 初始化为总帧数长度
            "font_size": 12,
            "position": (0, self.stage_height + 1.5),
            "durations": {}  # 存储每个时间点的持续时间：{start_frame: duration_frames}
        }
        
        # 存储演员和道具信息
        self.actors = []
        self.props = []
        
        # 拖动状态
        self.dragging = False
        self.drag_item = None
        self.drag_type = None  # 'actor' 或 'prop'
        self.drag_index = None
        self.drag_start_pos = None
        self.drag_end_pos = None
        self.last_dragged_item = None  # 保存最后拖动的项目
        self.last_dragged_pos = None   # 保存最后拖动的位置
        
        # 时间轴控制
        self.is_time_scale_updating = False  # 添加标志位防止递归
        self.is_user_dragging_timeline = False  # 标志位：用户是否正在拖动时间轴
        self.snap_interval = 1.0  # 滑块吸附间隔，默认1秒
        
        # 临时位置覆盖机制
        self.temp_position_overrides = {}  # 用于存储临时位置覆盖
        
        # 临时关键帧管理
        self.temp_keyframes = {}  # 存储临时关键帧 {(element_id, frame): True}
        
        # 固定视图范围 - 用于播放期间保持视图不变
        self.fixed_view_range = None  # 格式: {'xlim': (xmin, xmax), 'ylim': (ymin, ymax)}
        self.is_playing = False  # 播放状态标志
        
        # 缩放控制
        self.zoom_scale = 1.0  # 缩放比例，1.0表示原始大小
        self.min_zoom = 0.3  # 最小缩放比例（30%）
        self.max_zoom = 3.0  # 最大缩放比例（300%）
        
        # 视图平移控制
        self.pan_active = False  # 是否正在平移视图
        self.pan_start = None  # 平移起始位置（数据坐标）
        self.view_center = None  # 视图中心位置（用于平移后保持）
        
        # 撤销/重做历史记录系统
        self.history_stack = []  # 历史状态栈，最多保存20个状态
        self.redo_stack = []  # 重做栈，用于Ctrl+Y重做
        self.max_history = 20  # 最大历史记录数
        self._drag_history_saved = False  # 拖动历史保存标志
        
        # 颜色映射字典
        self.color_map = {
            "红色": "red",
            "蓝色": "blue",
            "绿色": "green",
            "紫色": "purple",
            "橙色": "orange",
            "棕色": "brown"
        }
        
        # 创建主框架
        self.main_frame = ttk.Frame(root)
        self.main_frame.pack(fill=tk.BOTH, expand=True)
        
        # 创建控制面板
        self.create_control_panel()
        
        # 创建舞台预览
        self.create_stage_preview()
        
        # 创建时间轴
        self.create_timeline()
        
        # 添加动画循环
        self.animation_loop = AnimationLoop(self)
        
        # 绑定窗口关闭事件
        self.root.protocol("WM_DELETE_WINDOW", self.on_closing)
        
        # 绑定Ctrl+Z撤销快捷键
        self.root.bind('<Control-z>', self.undo_last_operation)
        self.root.bind('<Control-Z>', self.undo_last_operation)
        
        # 绑定Ctrl+Y重做快捷键
        self.root.bind('<Control-y>', self.redo_last_operation)
        self.root.bind('<Control-Y>', self.redo_last_operation)
        
        # 显示欢迎消息
        self.log("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━", 'info')
        self.log("欢迎使用舞台走位动画制作工具 v2.3", 'info')
        self.log("", 'info')
        self.log("📌 快捷键操作:", 'info')
        self.log("  • Ctrl+Z 撤销 | Ctrl+Y 重做 | 空格 播放/暂停", 'info')
        self.log("", 'info')
        self.log("🖱️ 画布操作:", 'info')
        self.log("  • 滚轮 缩放舞台 (30%-300%)", 'info')
        self.log("  • 右键拖动 平移画布", 'info')
        self.log("  • 双击右键 重置视图", 'info')
        self.log("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━", 'info')
        
        # 标记窗口初始化完成
        self.window_initialized = True

    def save_state_to_history(self, operation_name="操作"):
        """保存当前状态到历史记录
        
        Args:
            operation_name: 操作名称，用于调试和显示
        """
        import copy
        
        # 创建当前状态的深拷贝
        state = {
            'operation': operation_name,
            'actors': copy.deepcopy(self.actors),
            'props': copy.deepcopy(self.props),
            'text_box': copy.deepcopy(self.text_box),
            'current_frame': self.current_frame,
            'current_second': self.current_second
        }
        
        # 添加到历史栈
        self.history_stack.append(state)
        
        # 如果超过最大历史记录数，删除最旧的记录
        if len(self.history_stack) > self.max_history:
            self.history_stack.pop(0)
        
        # 清空重做栈（新操作会使重做历史失效）
        self.redo_stack.clear()
        
        print(f"💾 已保存状态: {operation_name} (历史: {len(self.history_stack)}/{self.max_history})")
    
    def restore_state_from_history(self, state):
        """从历史记录恢复状态
        
        Args:
            state: 要恢复的状态字典
        """
        import copy
        
        # 恢复演员、道具和文本框状态
        self.actors = copy.deepcopy(state['actors'])
        self.props = copy.deepcopy(state['props'])
        self.text_box = copy.deepcopy(state['text_box'])
        self.current_frame = state['current_frame']
        self.current_second = state['current_second']
        
        # 更新UI
        self.time_scale.set(self.current_second)
        
        # 更新演员和道具列表
        self.keyframe_listbox.delete(0, tk.END)
        for actor in self.actors:
            self.keyframe_listbox.insert(tk.END, f"演员: {actor['name']}")
        for prop in self.props:
            self.keyframe_listbox.insert(tk.END, f"道具: {prop['name']}")
        
        # 更新文本框显示
        self.text_content_entry.delete(0, tk.END)
        if (self.current_frame < len(self.text_box["contents"]) and 
            self.current_frame >= 0):
            self.text_content_entry.insert(0, self.text_box["contents"][self.current_frame])
        
        # 更新时间显示
        self.text_second_entry.delete(0, tk.END)
        self.text_second_entry.insert(0, str(int(self.current_second)))
        
        # 更新持续时间显示
        self.text_duration_entry.delete(0, tk.END)
        current_duration = self.get_text_duration_at_frame(self.current_frame)
        self.text_duration_entry.insert(0, str(current_duration))
        
        # 更新舞台预览
        self.update_stage_preview()
        
        # 刷新关键帧列表
        self.on_keyframe_list_select(None)
        
        print(f"♻️ 已恢复状态: {state['operation']}")
    
    def undo_last_operation(self, event=None):
        """撤销上一步操作 (Ctrl+Z)"""
        if len(self.history_stack) == 0:
            self.log("⚠️ 没有可以撤销的操作", 'warning')
            return
        
        import copy
        
        # 保存当前状态到重做栈
        current_state = {
            'operation': '当前状态',
            'actors': copy.deepcopy(self.actors),
            'props': copy.deepcopy(self.props),
            'text_box': copy.deepcopy(self.text_box),
            'current_frame': self.current_frame,
            'current_second': self.current_second
        }
        self.redo_stack.append(current_state)
        
        # 限制重做栈大小
        if len(self.redo_stack) > self.max_history:
            self.redo_stack.pop(0)
        
        # 弹出最后一个状态（即当前状态之前的状态）
        last_state = self.history_stack.pop()
        
        # 恢复到该状态
        self.restore_state_from_history(last_state)
        
        self.log(f"↶ 已撤销: {last_state['operation']}", 'undo')
        print(f"↶ 撤销完成 (可重做: {len(self.redo_stack)})")
        
        # 返回"break"以阻止事件继续传播
        return "break"
    
    def redo_last_operation(self, event=None):
        """重做上一步撤销的操作 (Ctrl+Y)"""
        if len(self.redo_stack) == 0:
            self.log("⚠️ 没有可以重做的操作", 'warning')
            return
        
        import copy
        
        # 保存当前状态到历史栈
        current_state = {
            'operation': '当前状态',
            'actors': copy.deepcopy(self.actors),
            'props': copy.deepcopy(self.props),
            'text_box': copy.deepcopy(self.text_box),
            'current_frame': self.current_frame,
            'current_second': self.current_second
        }
        self.history_stack.append(current_state)
        
        # 限制历史栈大小
        if len(self.history_stack) > self.max_history:
            self.history_stack.pop(0)
        
        # 弹出重做栈的最后一个状态
        redo_state = self.redo_stack.pop()
        
        # 恢复到该状态
        self.restore_state_from_history(redo_state)
        
        self.log("↷ 已重做上一步撤销的操作", 'undo')
        print(f"↷ 重做完成 (可撤销: {len(self.history_stack)})")
        
        # 返回"break"以阻止事件继续传播
        return "break"
    
    def log(self, message, level='info'):
        """输出日志到日志窗口
        
        Args:
            message: 日志消息
            level: 日志级别 ('info', 'success', 'warning', 'error', 'undo')
        """
        import datetime
        
        # 获取当前时间
        timestamp = datetime.datetime.now().strftime('%H:%M:%S')
        
        # 格式化消息
        formatted_message = f"[{timestamp}] {message}\n"
        
        # 保存当前的yview位置
        current_yview = self.log_text.yview()
        
        # 启用编辑
        self.log_text.config(state='normal')
        
        # 限制日志行数，防止无限增长导致性能问题
        line_count = int(self.log_text.index('end-1c').split('.')[0])
        if line_count > 100:  # 最多保留100行日志
            self.log_text.delete('1.0', '2.0')  # 删除第一行
        
        # 添加日志
        self.log_text.insert(tk.END, formatted_message, level)
        
        # 自动滚动到最后
        self.log_text.see(tk.END)
        
        # 禁用编辑
        self.log_text.config(state='disabled')
        
        # 强制更新idle任务，但不调用update()避免窗口重新布局
        self.log_text.update_idletasks()
        
        # 同时输出到控制台（可选）
        print(formatted_message.strip())
    
    def on_closing(self):
        """处理窗口关闭事件"""
        # 停止音频播放
        if self.audio_file:
            pygame.mixer.music.stop()
        # 退出pygame
        pygame.mixer.quit()
        # 关闭窗口
        self.root.destroy()

    def create_control_panel(self):
        # 创建主控制面板框架，设置固定宽度
        control_frame = ttk.LabelFrame(self.main_frame, text="控制面板", width=300)
        control_frame.pack(side=tk.LEFT, fill=tk.Y, padx=5, pady=5)
        control_frame.pack_propagate(False)  # 禁止子组件改变父容器大小
        
        # 创建可滚动的Canvas
        canvas = tk.Canvas(control_frame, width=280)
        scrollbar = ttk.Scrollbar(control_frame, orient="vertical", command=canvas.yview)
        self.scrollable_frame = ttk.Frame(canvas)
        
        # 配置滚动区域
        self.scrollable_frame.bind(
            "<Configure>",
            lambda e: canvas.configure(scrollregion=canvas.bbox("all"))
        )
        
        # 创建窗口对象
        canvas.create_window((0, 0), window=self.scrollable_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)
        
        # 打包Canvas和滚动条
        canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")
        
        # 绑定鼠标滚轮事件
        def _on_mousewheel(event):
            # 兼容不同操作系统的滚轮事件
            if event.delta:
                # Windows和macOS
                canvas.yview_scroll(int(-1*(event.delta/120)), "units")
            else:
                # Linux
                if event.num == 4:
                    canvas.yview_scroll(-1, "units")
                elif event.num == 5:
                    canvas.yview_scroll(1, "units")
        
        # 绑定滚轮事件到canvas
        canvas.bind("<MouseWheel>", _on_mousewheel)  # Windows和macOS
        canvas.bind("<Button-4>", _on_mousewheel)    # Linux上滚
        canvas.bind("<Button-5>", _on_mousewheel)    # Linux下滚
        
        # 递归绑定所有子控件的滚轮事件
        def bind_mousewheel_to_children(widget):
            widget.bind("<MouseWheel>", _on_mousewheel)
            widget.bind("<Button-4>", _on_mousewheel)
            widget.bind("<Button-5>", _on_mousewheel)
            for child in widget.winfo_children():
                bind_mousewheel_to_children(child)
        
        # 延迟绑定，确保所有控件都已创建
        def delayed_bind():
            bind_mousewheel_to_children(self.scrollable_frame)
        
        canvas.after(100, delayed_bind)
        
        # 现在所有控件都添加到self.scrollable_frame而不是control_frame
        
        # 舞台设置
        stage_frame = ttk.LabelFrame(self.scrollable_frame, text="舞台设置")
        stage_frame.pack(fill=tk.X, padx=5, pady=5)
        
        ttk.Label(stage_frame, text="宽度:").grid(row=0, column=0, padx=5, pady=2)
        self.width_entry = ttk.Entry(stage_frame, width=10)
        self.width_entry.insert(0, str(self.stage_width))
        self.width_entry.grid(row=0, column=1, padx=5, pady=2)
        
        ttk.Label(stage_frame, text="高度:").grid(row=1, column=0, padx=5, pady=2)
        self.height_entry = ttk.Entry(stage_frame, width=10)
        self.height_entry.insert(0, str(self.stage_height))
        self.height_entry.grid(row=1, column=1, padx=5, pady=2)
        
        # 添加应用按钮
        ttk.Button(stage_frame, text="应用", command=self.update_stage_size).grid(row=2, column=0, columnspan=2, pady=5)
        
        # 时间轴设置
        timeline_frame = ttk.LabelFrame(self.scrollable_frame, text="时间轴设置")
        timeline_frame.pack(fill=tk.X, padx=5, pady=5)
        
        ttk.Label(timeline_frame, text="总秒数:").grid(row=0, column=0, padx=5, pady=2)
        self.seconds_entry = ttk.Entry(timeline_frame, width=10)
        self.seconds_entry.insert(0, str(self.total_seconds))
        self.seconds_entry.grid(row=0, column=1, padx=5, pady=2)
        
        # 添加播放速度设置
        ttk.Label(timeline_frame, text="播放速度:").grid(row=1, column=0, padx=5, pady=2)
        self.speed_var = tk.StringVar(value=str(self.playback_speed))
        self.speed_combo = ttk.Combobox(timeline_frame, textvariable=self.speed_var, 
                                      values=[f"{x:.2f}x" for x in self.speed_options],
                                      width=7, state="readonly")
        self.speed_combo.grid(row=1, column=1, padx=5, pady=2)
        self.speed_combo.bind('<<ComboboxSelected>>', self.on_speed_change)
        
        ttk.Button(timeline_frame, text="应用", command=self.update_timeline_settings).grid(row=2, column=0, columnspan=2, pady=5)
        
        # 在时间轴设置区域添加导出设置
        ttk.Label(timeline_frame, text="导出帧率:").grid(row=3, column=0, padx=5, pady=2)
        self.export_fps_entry = ttk.Entry(timeline_frame, width=10)
        self.export_fps_entry.insert(0, "10")  # 默认导出帧率
        self.export_fps_entry.grid(row=3, column=1, padx=5, pady=2)
        
        # 添加文本框区域
        text_frame = ttk.LabelFrame(self.scrollable_frame, text="文本框设置")
        text_frame.pack(fill=tk.X, padx=5, pady=5)
        
        ttk.Label(text_frame, text="时间(秒):").grid(row=0, column=0, padx=5, pady=2)
        self.text_second_entry = ttk.Entry(text_frame, width=10)
        self.text_second_entry.insert(0, str(self.current_second))
        self.text_second_entry.grid(row=0, column=1, padx=5, pady=2)
        
        ttk.Label(text_frame, text="文本内容:").grid(row=1, column=0, padx=5, pady=2)
        self.text_content_entry = ttk.Entry(text_frame, width=20)
        self.text_content_entry.grid(row=1, column=1, padx=5, pady=2)
        
        ttk.Label(text_frame, text="字体大小:").grid(row=2, column=0, padx=5, pady=2)
        self.text_size_entry = ttk.Entry(text_frame, width=10)
        self.text_size_entry.insert(0, str(self.text_box["font_size"]))
        self.text_size_entry.grid(row=2, column=1, padx=5, pady=2)
        
        ttk.Label(text_frame, text="持续时间(秒):").grid(row=3, column=0, padx=5, pady=2)
        self.text_duration_entry = ttk.Entry(text_frame, width=10)
        self.text_duration_entry.insert(0, "1")  # 默认1秒
        self.text_duration_entry.grid(row=3, column=1, padx=5, pady=2)
        
        # 添加应用按钮
        ttk.Button(text_frame, text="应用", command=self.update_text_box).grid(row=4, column=0, columnspan=2, pady=5)
        
        # 添加演员/道具区域
        add_frame = ttk.LabelFrame(self.scrollable_frame, text="添加演员/道具")
        add_frame.pack(fill=tk.X, padx=5, pady=5)
        
        # 演员设置
        actor_frame = ttk.LabelFrame(add_frame, text="演员设置")
        actor_frame.pack(fill=tk.X, padx=5, pady=5)
        
        # 名称和字号在同一行
        name_size_frame = ttk.Frame(actor_frame)
        name_size_frame.grid(row=0, column=0, columnspan=2, padx=5, pady=2)
        
        ttk.Label(name_size_frame, text="名称:").pack(side=tk.LEFT, padx=2)
        self.actor_name_entry = ttk.Entry(name_size_frame, width=8)
        self.actor_name_entry.pack(side=tk.LEFT, padx=2)
        
        ttk.Label(name_size_frame, text="字号:").pack(side=tk.LEFT, padx=2)
        self.actor_font_size = ttk.Entry(name_size_frame, width=4)
        self.actor_font_size.insert(0, "10")  # 默认字号
        self.actor_font_size.pack(side=tk.LEFT, padx=2)
        
        # 隐藏形状选择但保留功能
        self.actor_shape_var = tk.StringVar(value="circle")
        self.actor_shape_combo = ttk.Combobox(actor_frame, textvariable=self.actor_shape_var, 
                                            values=["circle", "square", "triangle"], width=7)
        # 不调用grid方法，使控件不可见
        
        ttk.Label(actor_frame, text="大小(直径):").grid(row=1, column=0, padx=5, pady=2)
        self.actor_size_entry = ttk.Entry(actor_frame, width=10)
        self.actor_size_entry.insert(0, "1.0")  # 默认直径为1.0
        self.actor_size_entry.grid(row=1, column=1, padx=5, pady=2)
        
        # 添加颜色选择
        ttk.Label(actor_frame, text="颜色:").grid(row=2, column=0, padx=5, pady=2)
        self.actor_color_var = tk.StringVar(value="蓝色")
        self.actor_color_combo = ttk.Combobox(actor_frame, textvariable=self.actor_color_var, 
                                            values=["蓝色", "红色", "绿色", "紫色", "橙色", "棕色"], 
                                            width=7, state="readonly")
        self.actor_color_combo.grid(row=2, column=1, padx=5, pady=2)
        
        # 添加演员按钮和删除演员按钮
        actor_btn_frame = ttk.Frame(actor_frame)
        actor_btn_frame.grid(row=3, column=0, columnspan=2, pady=5)
        ttk.Button(actor_btn_frame, text="添加演员", command=self.add_actor).pack(side=tk.LEFT, padx=2)
        ttk.Button(actor_btn_frame, text="删除演员", command=self.delete_actor).pack(side=tk.LEFT, padx=2)
        
        # 道具设置
        prop_frame = ttk.LabelFrame(add_frame, text="道具设置")
        prop_frame.pack(fill=tk.X, padx=5, pady=5)
        
        # 名称和字号在同一行
        prop_name_size_frame = ttk.Frame(prop_frame)
        prop_name_size_frame.grid(row=0, column=0, columnspan=2, padx=5, pady=2)
        
        ttk.Label(prop_name_size_frame, text="名称:").pack(side=tk.LEFT, padx=2)
        self.prop_name_entry = ttk.Entry(prop_name_size_frame, width=8)
        self.prop_name_entry.pack(side=tk.LEFT, padx=2)
        
        ttk.Label(prop_name_size_frame, text="字号:").pack(side=tk.LEFT, padx=2)
        self.prop_font_size = ttk.Entry(prop_name_size_frame, width=4)
        self.prop_font_size.insert(0, "10")  # 默认字号
        self.prop_font_size.pack(side=tk.LEFT, padx=2)
        
        # 隐藏形状选择但保留功能
        self.prop_shape_var = tk.StringVar(value="rectangle")
        self.prop_shape_combo = ttk.Combobox(prop_frame, textvariable=self.prop_shape_var, 
                                           values=["rectangle", "circle", "triangle"], width=7)
        # 不调用grid方法，使控件不可见
        
        ttk.Label(prop_frame, text="宽度:").grid(row=1, column=0, padx=5, pady=2)
        self.prop_width_entry = ttk.Entry(prop_frame, width=10)
        self.prop_width_entry.insert(0, "1.0")
        self.prop_width_entry.grid(row=1, column=1, padx=5, pady=2)
        
        ttk.Label(prop_frame, text="高度:").grid(row=2, column=0, padx=5, pady=2)
        self.prop_height_entry = ttk.Entry(prop_frame, width=10)
        self.prop_height_entry.insert(0, "1.0")
        self.prop_height_entry.grid(row=2, column=1, padx=5, pady=2)
        
        # 添加颜色选择
        ttk.Label(prop_frame, text="颜色:").grid(row=3, column=0, padx=5, pady=2)
        self.prop_color_var = tk.StringVar(value="红色")
        self.prop_color_combo = ttk.Combobox(prop_frame, textvariable=self.prop_color_var, 
                                           values=["红色", "蓝色", "绿色", "紫色", "橙色", "棕色"], 
                                           width=7, state="readonly")
        self.prop_color_combo.grid(row=3, column=1, padx=5, pady=2)
        
        # 添加道具按钮和删除道具按钮
        prop_btn_frame = ttk.Frame(prop_frame)
        prop_btn_frame.grid(row=4, column=0, columnspan=2, pady=5)
        ttk.Button(prop_btn_frame, text="添加道具", command=self.add_prop).pack(side=tk.LEFT, padx=2)
        ttk.Button(prop_btn_frame, text="删除道具", command=self.delete_prop).pack(side=tk.LEFT, padx=2)
        
        # 创建但不显示插入关键帧按钮
        self.insert_keyframe_btn = ttk.Button(self.scrollable_frame, text="插入关键帧", command=self.insert_keyframe, state='disabled')
        # 不调用pack()方法，按钮将不会显示在界面上

        # 批量插入关键帧按钮将在时间轴区域创建
        
    def import_audio(self):
        """导入音频文件"""
        try:
            # 让用户选择音频文件
            file_path = filedialog.askopenfilename(
                filetypes=[
                    ("音频文件", "*.wav;*.mp3"),
                    ("WAV文件", "*.wav"),
                    ("MP3文件", "*.mp3"),
                    ("所有文件", "*.*")
                ],
                title="导入音频"
            )
            
            if not file_path:  # 用户取消选择
                return
                
            # 停止当前播放的音频
            if self.audio_file:
                pygame.mixer.music.stop()
                pygame.mixer.music.unload()  # 先卸载旧音频
            
            # 加载新的音频文件
            try:
                pygame.mixer.music.load(file_path)
                # 设置音量
                pygame.mixer.music.set_volume(self.audio_volume)
                self.audio_file = file_path
                print(f"✅ 音频文件加载成功: {os.path.basename(file_path)}")
            except Exception as e:
                print(f"❌ 音频加载失败: {str(e)}")
                raise
            
            # 获取音频时长
            try:
                if file_path.lower().endswith('.wav'):
                    with contextlib.closing(wave.open(file_path, 'r')) as f:
                        frames = f.getnframes()
                        rate = f.getframerate()
                        self.audio_duration = frames / float(rate)
                else:
                    # 对于MP3文件，使用AudioFileClip获取时长（更可靠）
                    try:
                        audio_clip = AudioFileClip(file_path)
                        self.audio_duration = audio_clip.duration
                        audio_clip.close()
                    except:
                        # 如果失败，尝试使用pygame获取时长
                        sound = pygame.mixer.Sound(file_path)
                        self.audio_duration = sound.get_length()
                        del sound  # 释放资源
            except Exception as e:
                print(f"获取音频时长时出错: {str(e)}")
                # 如果无法获取准确时长，使用默认值
                self.audio_duration = 60  # 默认60秒
                messagebox.showwarning("警告", "无法获取音频时长，将使用默认值60秒")
            
            # 更新时间轴总秒数
            self.total_seconds = self.audio_duration
            self.total_frames = int(self.total_seconds * self.fps)
            
            # 更新UI显示
            self.seconds_entry.delete(0, tk.END)
            self.seconds_entry.insert(0, str(self.total_seconds))
            
            # 更新时间轴滑块
            self.time_scale.config(to=self.total_seconds)
            
            # 更新演员位置数组
            for actor in self.actors:
                old_positions = actor["positions"]
                actor["positions"] = [old_positions[0] for _ in range(self.total_frames)]  # 使用初始位置填充
                for i in range(min(len(old_positions), self.total_frames)):
                    actor["positions"][i] = old_positions[i]
                # 清理超出范围的关键帧
                actor["keyframes"] = [frame for frame in actor["keyframes"] if frame < self.total_frames]
                # 更新中间帧插值
                if len(actor["keyframes"]) >= 2:
                    self.update_intermediate_frames(actor)
            
            # 更新道具位置数组
            for prop in self.props:
                old_positions = prop["positions"]
                prop["positions"] = [old_positions[0] for _ in range(self.total_frames)]  # 使用初始位置填充
                for i in range(min(len(old_positions), self.total_frames)):
                    prop["positions"][i] = old_positions[i]
                # 清理超出范围的关键帧
                prop["keyframes"] = [frame for frame in prop["keyframes"] if frame < self.total_frames]
                # 更新中间帧插值
                if len(prop["keyframes"]) >= 2:
                    self.update_intermediate_frames(prop)
            
            # 更新文本框内容数组
            old_contents = self.text_box["contents"]
            self.text_box["contents"] = ["" for _ in range(self.total_frames)]
            for i in range(min(len(old_contents), self.total_frames)):
                self.text_box["contents"][i] = old_contents[i]
            
            # 重置当前帧和时间
            self.current_frame = 0
            self.current_second = 0
            
            # 停止任何正在进行的动画
            if hasattr(self, 'animation_loop') and self.animation_loop.running:
                self.animation_loop.stop()
            
            # 重置拖动状态
            self.dragging = False
            self.drag_item = None
            self.drag_type = None
            self.drag_index = None
            self.drag_start_pos = None
            self.drag_end_pos = None
            
            # 重置时间轴滑块标志
            self.is_time_scale_updating = False
            
            # 更新时间轴滑块位置
            self.time_scale.set(0)
            
            # 更新显示
            self.update_stage_preview()
            
            # 强制更新画布
            self.canvas.draw()
            
            # 显示成功消息
            self.log(f"✓ 音频已导入，时长: {self.audio_duration:.2f}秒", 'success')
            
            # 启用删除音频按钮
            if hasattr(self, 'remove_audio_btn'):
                self.remove_audio_btn.config(state='normal')
            
        except Exception as e:
            error_msg = f"导入音频失败: {str(e)}"
            print(error_msg)  # 打印详细错误信息
            messagebox.showerror("错误", error_msg)

    def play_audio(self):
        """播放音频"""
        if self.audio_file:
            pygame.mixer.music.play(loops=0, start=self.current_second)

    def pause_audio(self):
        """暂停音频"""
        if self.audio_file:
            pygame.mixer.music.pause()

    def stop_audio(self):
        """停止音频"""
        if self.audio_file:
            pygame.mixer.music.stop()
            self.current_second = 0
            self.current_frame = 0
            self.time_scale.set(0)
            self.update_stage_preview()

    def remove_audio(self):
        """删除导入的音频文件"""
        if not self.audio_file:
            self.log("⚠️ 当前没有导入的音频文件", 'warning')
            return
        
        # 确认删除
        result = messagebox.askyesno("确认删除", 
                                       f"确定要删除音频文件吗？\n\n文件: {os.path.basename(self.audio_file)}\n\n注意：删除后将无法使用带音频导出功能。")
        
        if not result:
            return
        
        try:
            # 停止当前播放的音频
            if self.audio_file:
                pygame.mixer.music.stop()
            
            # 停止任何正在进行的动画
            if hasattr(self, 'animation_loop') and self.animation_loop.running:
                self.animation_loop.stop()
            
            # 清除音频文件引用
            old_audio_file = self.audio_file
            self.audio_file = None
            self.audio_duration = 0
            
            # 重置当前帧和时间到开始位置
            self.current_frame = 0
            self.current_second = 0
            
            # 重置拖动状态
            self.dragging = False
            self.drag_item = None
            self.drag_type = None
            self.drag_index = None
            self.drag_start_pos = None
            self.drag_end_pos = None
            
            # 重置时间轴滑块标志
            self.is_time_scale_updating = False
            
            # 更新时间轴滑块位置到开始
            self.time_scale.set(0)
            
            # 更新文本框时间显示
            self.text_second_entry.delete(0, tk.END)
            self.text_second_entry.insert(0, "0")
            
            # 更新文本框内容显示
            self.text_content_entry.delete(0, tk.END)
            if self.text_box["contents"]:
                self.text_content_entry.insert(0, self.text_box["contents"][0])
            
            # 更新持续时间显示
            self.text_duration_entry.delete(0, tk.END)
            current_duration = self.get_text_duration_at_frame(0)
            self.text_duration_entry.insert(0, str(current_duration))
            
            # 更新显示
            self.update_stage_preview()
            
            # 强制更新画布
            self.canvas.draw()
            
            # 显示成功消息
            self.log(f"✓ 音频文件已删除: {os.path.basename(old_audio_file)}", 'success')
            
            # 禁用删除音频按钮
            if hasattr(self, 'remove_audio_btn'):
                self.remove_audio_btn.config(state='disabled')
            
        except Exception as e:
            error_msg = f"删除音频失败: {str(e)}"
            print(error_msg)  # 打印详细错误信息
            messagebox.showerror("错误", error_msg)

    def create_stage_preview(self):
        # 创建中间区域的容器
        center_frame = ttk.Frame(self.main_frame)
        center_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # 创建舞台预览
        preview_frame = ttk.LabelFrame(center_frame, text="舞台预览")
        preview_frame.pack(fill=tk.BOTH, expand=True, pady=(0, 5))
        
        # 创建matplotlib图形 - 不固定大小，让它自适应容器
        self.fig = Figure()
        self.ax = self.fig.add_subplot(111)
        self.canvas = FigureCanvasTkAgg(self.fig, master=preview_frame)
        self.canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        
        # 设置图形布局参数（使用 subplots_adjust 而不是 tight_layout，避免窗口移动）
        # left, bottom, right, top 分别表示子图区域的边界（0-1之间的比例）
        self.fig.subplots_adjust(left=0.08, bottom=0.08, right=0.95, top=0.95)
        
        # 初始化舞台显示
        self.update_stage_preview()
        
        # 添加鼠标事件处理
        self.canvas.mpl_connect('button_press_event', self.on_mouse_press)
        self.canvas.mpl_connect('button_release_event', self.on_mouse_release)
        self.canvas.mpl_connect('motion_notify_event', self.on_mouse_move)
        self.canvas.mpl_connect('scroll_event', self.on_mouse_scroll)  # 添加滚轮事件
        
        # 创建时间轴区域 - 在舞台预览下方
        timeline_frame = ttk.LabelFrame(center_frame, text="时间轴")
        timeline_frame.pack(fill=tk.X, pady=(5, 0))
        
        # 添加自定义标尺控制区域
        snap_frame = ttk.Frame(timeline_frame)
        snap_frame.pack(fill=tk.X, padx=5, pady=2)
        
        # 滑块吸附间隔输入
        ttk.Label(snap_frame, text="滑块吸附间隔(秒):").pack(side=tk.LEFT, padx=2)
        self.snap_interval_entry = ttk.Entry(snap_frame, width=5)
        self.snap_interval_entry.pack(side=tk.LEFT, padx=2)
        self.snap_interval_entry.insert(0, "1.0")  # 默认1.0秒（小数点后1位）
        # 使用FocusOut和Return事件，而不是KeyRelease，允许用户完整输入
        self.snap_interval_entry.bind('<FocusOut>', self.on_snap_interval_change)
        self.snap_interval_entry.bind('<Return>', self.on_snap_interval_change)
        
        # 自定义标尺间隔输入
        ttk.Label(snap_frame, text="自定义标尺间隔(秒):").pack(side=tk.LEFT, padx=(20, 2))
        self.custom_interval_entry = ttk.Entry(snap_frame, width=5)
        self.custom_interval_entry.pack(side=tk.LEFT, padx=2)
        self.custom_interval_entry.insert(0, "5")  # 默认5秒
        self.custom_interval_entry.bind('<KeyRelease>', self.on_custom_interval_change)
        
        # 标尺开关按钮
        self.ruler_enabled = tk.BooleanVar(value=False)
        ruler_checkbox = ttk.Checkbutton(snap_frame, text="显示标尺", 
                                       variable=self.ruler_enabled,
                                       command=self.on_ruler_toggle)
        ruler_checkbox.pack(side=tk.LEFT, padx=10)
        
        # 批量插入关键帧按钮
        self.batch_insert_keyframe_btn = ttk.Button(snap_frame, text="批量插入关键帧", command=self.batch_insert_keyframe)
        self.batch_insert_keyframe_btn.pack(side=tk.LEFT, padx=10)
        
        # 标尺显示容器 - 使用可滚动Canvas
        self.ruler_container = ttk.Frame(timeline_frame)
        # 默认不显示，只有在启用标尺时才显示
        
        # 创建Canvas用于横向滚动
        self.ruler_canvas = tk.Canvas(self.ruler_container, height=40, bg='white')
        self.ruler_scrollbar = ttk.Scrollbar(self.ruler_container, orient=tk.HORIZONTAL, command=self.ruler_canvas.xview)
        self.ruler_frame = ttk.Frame(self.ruler_canvas)
        
        # 配置Canvas
        self.ruler_canvas.configure(xscrollcommand=self.ruler_scrollbar.set)
        self.ruler_canvas.create_window((0, 0), window=self.ruler_frame, anchor='nw')
        
        # 绑定配置事件
        self.ruler_frame.bind('<Configure>', lambda e: self.ruler_canvas.configure(scrollregion=self.ruler_canvas.bbox('all')))
        
        # 布局（仅在显示标尺时pack）
        self.ruler_canvas.pack(side=tk.TOP, fill=tk.X, expand=False)
        self.ruler_scrollbar.pack(side=tk.TOP, fill=tk.X)
        
        # 时间轴滑块 - 使用tk.Scale替代ttk.Scale
        self.time_scale = tk.Scale(timeline_frame, 
                                 from_=0, 
                                 to=self.total_seconds,  # 修复：允许到达总秒数
                                 orient=tk.HORIZONTAL,
                                 command=self.on_time_scale_change,
                                 resolution=0.1,  # 设置分辨率为0.1秒，实现更平滑的播放
                                 showvalue=True,  # 显示当前值
                                 tickinterval=0)  # 设置刻度间隔为0，不显示刻度
        self.time_scale.pack(fill=tk.X, padx=5, pady=5)
        
        # 绑定鼠标事件以检测用户拖动
        self.time_scale.bind('<ButtonPress-1>', self.on_time_scale_press)
        self.time_scale.bind('<ButtonRelease-1>', self.on_time_scale_release)
        
        # 初始化标尺相关变量
        self.custom_interval = 5  # 默认自定义间隔5秒
        self.ruler_buttons = []  # 存储标尺按钮
        
        # 播放控制按钮
        control_frame = ttk.Frame(timeline_frame)
        control_frame.pack(fill=tk.X, padx=5, pady=5)
        
        # 创建播放控制按钮并绑定事件
        print("正在创建播放按钮...")  # 调试信息
        self.play_button = ttk.Button(control_frame, text="播放", command=self.play_animation)
        self.play_button.pack(side=tk.LEFT, padx=5)
        print("播放按钮创建完成")  # 调试信息
        
        print("正在创建暂停按钮...")  # 调试信息
        self.pause_button = ttk.Button(control_frame, text="暂停", command=self.pause_animation)
        self.pause_button.pack(side=tk.LEFT, padx=5)
        print("暂停按钮创建完成")  # 调试信息
        
        print("正在创建停止按钮...")  # 调试信息
        self.stop_button = ttk.Button(control_frame, text="停止", command=self.stop_animation)
        self.stop_button.pack(side=tk.LEFT, padx=5)
        print("停止按钮创建完成")  # 调试信息
        
        # 创建切换时间控件组
        switch_frame = ttk.Frame(control_frame)
        switch_frame.pack(side=tk.LEFT, padx=5)
        ttk.Label(switch_frame, text="切换时间(秒):").pack(side=tk.LEFT, padx=2)
        self.frame_switch_entry = ttk.Entry(switch_frame, width=8)
        self.frame_switch_entry.pack(side=tk.LEFT, padx=2)
        ttk.Button(switch_frame, text="切换", command=self.switch_frame).pack(side=tk.LEFT, padx=2)
        
        # 创建音量控制区域
        volume_frame = ttk.Frame(control_frame)
        volume_frame.pack(side=tk.RIGHT, padx=5)
        ttk.Label(volume_frame, text="音量:").pack(side=tk.LEFT, padx=2)
        self.volume_scale = ttk.Scale(volume_frame, 
                                    from_=0, 
                                    to=100,
                                    orient=tk.HORIZONTAL,
                                    value=50,  # 默认音量50%
                                    length=100,  # 设置滑块长度
                                    command=self.on_volume_change)
        self.volume_scale.pack(side=tk.LEFT, padx=2)
        
    def create_timeline(self):
        # 创建右侧面板，设置固定宽度避免跳动
        right_frame = ttk.Frame(self.main_frame, width=450)
        right_frame.pack(side=tk.RIGHT, fill=tk.Y, padx=5, pady=5)
        right_frame.pack_propagate(False)  # 禁止子组件改变父容器大小
        
        # 创建关键帧编辑区域，限制最大高度
        keyframe_frame = ttk.LabelFrame(right_frame, text="关键帧编辑")
        keyframe_frame.pack(fill=tk.BOTH, expand=True, pady=5)
        keyframe_frame.pack_propagate(True)  # 允许自适应，但受右侧面板限制
        
        # 创建左侧列表
        list_frame = ttk.Frame(keyframe_frame)
        list_frame.pack(side=tk.LEFT, fill=tk.Y, padx=5, pady=5)
        
        ttk.Label(list_frame, text="演员和道具列表").pack()
        
        # 创建列表框
        self.keyframe_listbox = tk.Listbox(list_frame, width=20, height=10)
        self.keyframe_listbox.pack(fill=tk.Y, expand=True)
        
        # 创建右侧编辑区域
        self.edit_frame = ttk.Frame(keyframe_frame)
        self.edit_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # 当前选中项信息
        self.current_item_label = ttk.Label(self.edit_frame, text="请选择要编辑的演员或道具")
        self.current_item_label.pack(pady=5)
        
        # 创建关键帧表格
        columns = ('时间点', 'X坐标', 'Y坐标')
        self.keyframe_tree = ttk.Treeview(self.edit_frame, columns=columns, show='headings', height=10)
        
        # 设置列标题
        for col in columns:
            self.keyframe_tree.heading(col, text=col)
            self.keyframe_tree.column(col, width=80)
            
        self.keyframe_tree.pack(fill=tk.BOTH, expand=True, pady=5)
        
        # 添加滚动条
        scrollbar = ttk.Scrollbar(self.edit_frame, orient=tk.VERTICAL, command=self.keyframe_tree.yview)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.keyframe_tree.configure(yscrollcommand=scrollbar.set)
        
        # 添加按钮
        button_frame = ttk.Frame(self.edit_frame)
        button_frame.pack(fill=tk.X, pady=5)
        
        ttk.Button(button_frame, text="添加关键帧", command=self.add_keyframe).pack(side=tk.LEFT, padx=5)
        ttk.Button(button_frame, text="删除关键帧", command=self.delete_keyframe).pack(side=tk.LEFT, padx=5)
        
        # 重置操作按钮行
        reset_frame = ttk.Frame(self.edit_frame)
        reset_frame.pack(fill=tk.X, pady=2)
        
        ttk.Button(reset_frame, text="重置到等候区", command=self.reset_to_waiting_area).pack(side=tk.LEFT, padx=5)
        ttk.Button(reset_frame, text="全部重置", command=self.reset_all_to_waiting_area).pack(side=tk.LEFT, padx=5)
        
        # 绑定事件
        self.keyframe_listbox.bind('<<ListboxSelect>>', self.on_keyframe_list_select)
        
        # 项目操作区域 - 移到原来作者信息的位置
        project_frame = ttk.LabelFrame(right_frame, text="项目操作")
        project_frame.pack(fill=tk.X, pady=5)
        
        # 将所有项目操作按钮放在同一行
        project_row = ttk.Frame(project_frame)
        project_row.pack(fill=tk.X, padx=5, pady=3)
        
        self.save_btn = ttk.Button(project_row, text="保存项目", command=self.save_project)
        self.save_btn.pack(side=tk.LEFT, padx=2)
        
        self.load_btn = ttk.Button(project_row, text="导入项目", command=self.load_project)
        self.load_btn.pack(side=tk.LEFT, padx=2)
        
        self.audio_btn = ttk.Button(project_row, text="导入音频", command=self.import_audio)
        self.audio_btn.pack(side=tk.LEFT, padx=2)
        
        self.remove_audio_btn = ttk.Button(project_row, text="删除音频", command=self.remove_audio)
        self.remove_audio_btn.pack(side=tk.LEFT, padx=2)
        
        # 初始状态：如果没有音频文件，禁用删除按钮
        if not hasattr(self, 'audio_file') or not self.audio_file:
            self.remove_audio_btn.config(state='disabled')
        
        # 导出操作区域
        export_frame = ttk.LabelFrame(right_frame, text="导出操作")
        export_frame.pack(fill=tk.X, padx=5, pady=5)
        
        # 将所有导出操作按钮放在同一行
        export_row = ttk.Frame(export_frame)
        export_row.pack(fill=tk.X, padx=5, pady=3)
        
        self.export_btn = ttk.Button(export_row, text="导出GIF动画", command=self.export_animation)
        self.export_btn.pack(side=tk.LEFT, padx=2)
        
        self.export_with_audio_btn = ttk.Button(export_row, text="导出带音频MP4", command=self.export_animation_with_audio)
        self.export_with_audio_btn.pack(side=tk.LEFT, padx=2)
        
        # 创建日志输出窗口 - 在软件信息上方，固定高度
        log_frame = ttk.LabelFrame(right_frame, text="操作日志", height=180)
        log_frame.pack(fill=tk.X, pady=5)
        log_frame.pack_propagate(False)  # 禁止子组件改变容器大小
        
        # 创建Text组件用于显示日志，设置固定高度
        self.log_text = tk.Text(log_frame, height=10, width=50,  # 固定高度10行
                               font=('Consolas', 9),
                               bg='#2b2b2b', fg='#cccccc',
                               wrap=tk.WORD, state='disabled',
                               relief=tk.FLAT, borderwidth=0)
        self.log_text.pack(fill=tk.BOTH, expand=True, padx=2, pady=2)
        
        # 添加滚动条
        log_scrollbar = ttk.Scrollbar(self.log_text, orient=tk.VERTICAL, 
                                      command=self.log_text.yview)
        log_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.log_text.configure(yscrollcommand=log_scrollbar.set)
        
        # 配置文本标签样式
        self.log_text.tag_config('info', foreground='#7ec699')  # 绿色 - 普通信息
        self.log_text.tag_config('success', foreground='#5cb85c')  # 深绿 - 成功
        self.log_text.tag_config('warning', foreground='#f0ad4e')  # 橙色 - 警告
        self.log_text.tag_config('error', foreground='#d9534f')  # 红色 - 错误
        self.log_text.tag_config('undo', foreground='#5bc0de')  # 蓝色 - 撤销/重做
        
        # 创建作者信息区域 - 移到时间轴下面
        author_frame = ttk.LabelFrame(right_frame, text="软件信息")
        author_frame.pack(fill=tk.X, pady=5)
        
        # 作者信息文本
        author_info = """舞台走位动画制作工具 v2.3 测试版
由@天云 免费制作及分享
如有bug或好的优化建议，可联系：
QQ：1248360754 小红书：5615193523"""
        
        author_label = tk.Label(author_frame, text=author_info, 
                               justify='left', 
                               font=('Microsoft YaHei', 9),
                               fg='#333333',
                               bg='#f0f0f0',
                               padx=10, pady=8)
        author_label.pack(fill=tk.X, padx=5, pady=5)
        
        # 为所有按钮绑定空格键，调用我们的切换函数而不是按钮的默认行为
        # 使用lambda包装以防止事件传播到按钮的默认处理器
        def button_space_handler(e):
            self.toggle_play_pause(e)
            return "break"  # 阻止按钮的默认空格键行为
        
        self.root.bind_class("TButton", "<space>", button_space_handler)
        
        # 为非按钮区域也绑定空格键
        self.root.bind_all('<space>', self.toggle_play_pause)
        print("空格键已绑定到播放/暂停切换功能")

    def update_scale_labels(self):
        """更新时间轴刻度标签"""
        # 当前使用的tk.Scale本身有刻度显示功能，无需单独的刻度标签
        pass

    def on_keyframe_list_select(self, event):
        """处理关键帧列表选择事件"""
        selected = self.keyframe_listbox.curselection()
        if not selected:
            return
            
        index = selected[0]
        if index < len(self.actors):
            current_item = self.actors[index]
            self.current_item_label.config(text=f"当前编辑: 演员 {current_item['name']}")
        elif index < len(self.actors) + len(self.props):
            current_item = self.props[index - len(self.actors)]
            self.current_item_label.config(text=f"当前编辑: 道具 {current_item['name']}")
        else:
            current_item = self.text_box
            self.current_item_label.config(text=f"当前编辑: 文本框")
            
        # 清空现有数据
        for row in self.keyframe_tree.get_children():
            self.keyframe_tree.delete(row)
            
        # 添加关键帧数据
        for frame in sorted(current_item["keyframes"]):
            pos = current_item["positions"][frame]
            seconds = frame / self.fps  # 使用除法，支持小数
            # 插入数据时，使用tags保存原始帧数，避免浮点数精度问题
            item_id = self.keyframe_tree.insert('', 'end', 
                                                values=(f"{seconds:.1f}秒", f"{pos[0]:.1f}", f"{pos[1]:.1f}"))
            # 将原始帧数保存在item的tags中
            self.keyframe_tree.item(item_id, tags=(str(frame),))

    def update_keyframe_data(self):
        """更新关键帧数据"""
        selected = self.keyframe_listbox.curselection()
        if not selected:
            messagebox.showwarning("警告", "请先选择一个演员或道具")
            return
            
        index = selected[0]
        if index < len(self.actors):
            current_item = self.actors[index]
        else:
            current_item = self.props[index - len(self.actors)]
            
        try:
            # 获取所有行的值
            for item in self.keyframe_tree.get_children():
                values = self.keyframe_tree.item(item)['values']
                tags = self.keyframe_tree.item(item)['tags']
                
                # 从tags中获取原始帧数（避免浮点数精度问题）
                if tags and len(tags) > 0:
                    frame = int(tags[0])
                else:
                    # 兼容旧数据：如果没有tags，使用秒数计算
                    seconds = float(values[0].rstrip('秒'))
                    frame = int(seconds * self.fps)
                
                x = float(values[1])
                y = float(values[2])
                
                # 更新位置
                current_item["positions"][frame] = (x, y)
                
                # 确保时间点在关键帧列表中
                if frame not in current_item["keyframes"]:
                    current_item["keyframes"].append(frame)
                    current_item["keyframes"].sort()
                    
            # 更新中间帧
            self.update_intermediate_frames(current_item)
            
            # 更新舞台预览
            self.update_stage_preview()
            
            # 重新加载表格数据
            self.on_keyframe_list_select(None)
            
            # 显示成功提示
            messagebox.showinfo("成功", "关键帧数据已更新")
            
        except ValueError as e:
            messagebox.showerror("错误", str(e))

    def add_keyframe(self):
        """添加关键帧"""
        selected = self.keyframe_listbox.curselection()
        if not selected:
            messagebox.showwarning("警告", "请先选择一个演员或道具")
            return
            
        index = selected[0]
        if index < len(self.actors):
            current_item = self.actors[index]
        else:
            current_item = self.props[index - len(self.actors)]
            
        try:
            # 创建新窗口
            add_dialog = tk.Toplevel(self.root)
            add_dialog.title("添加关键帧")
            
            # 添加输入框
            ttk.Label(add_dialog, text="时间点(秒):").grid(row=0, column=0, padx=5, pady=2)
            time_entry = ttk.Entry(add_dialog)
            time_entry.grid(row=0, column=1, padx=5, pady=2)
            
            ttk.Label(add_dialog, text="X坐标:").grid(row=1, column=0, padx=5, pady=2)
            x_entry = ttk.Entry(add_dialog)
            x_entry.grid(row=1, column=1, padx=5, pady=2)
            
            ttk.Label(add_dialog, text="Y坐标:").grid(row=2, column=0, padx=5, pady=2)
            y_entry = ttk.Entry(add_dialog)
            y_entry.grid(row=2, column=1, padx=5, pady=2)
            
            def save_keyframe():
                try:
                    seconds = float(time_entry.get())  # 接受浮点数
                    # 四舍五入到小数点后1位
                    seconds = round(seconds, 1)
                    
                    if seconds < 0 or seconds >= self.total_seconds:
                        raise ValueError("时间点超出范围")
                        
                    frame = int(seconds * self.fps)  # 计算对应的帧数
                    x = float(x_entry.get())
                    y = float(y_entry.get())
                    
                    # 保存历史记录
                    self.save_state_to_history(f"添加关键帧 ({current_item['name']} @ {seconds}秒)")
                    
                    # 更新数据
                    current_item["positions"][frame] = (x, y)
                    if frame not in current_item["keyframes"]:
                        current_item["keyframes"].append(frame)
                        current_item["keyframes"].sort()
                        
                    # 更新中间帧插值
                    self.update_intermediate_frames(current_item)
                        
                    # 更新显示
                    self.on_keyframe_list_select(None)
                    
                    # 记录日志
                    self.log(f"✓ 添加关键帧: {current_item['name']} @ {seconds}秒", 'success')
                    
                    add_dialog.destroy()
                    
                except ValueError as e:
                    messagebox.showerror("错误", str(e))
                    
            ttk.Button(add_dialog, text="确定", command=save_keyframe).grid(row=3, column=0, columnspan=2, pady=10)
            
        except ValueError as e:
            messagebox.showerror("错误", str(e))
            
    def delete_keyframe(self):
        """删除关键帧"""
        selected = self.keyframe_listbox.curselection()
        if not selected:
            messagebox.showwarning("警告", "请先选择一个演员或道具")
            return
            
        index = selected[0]
        if index < len(self.actors):
            current_item = self.actors[index]
        else:
            current_item = self.props[index - len(self.actors)]
            
        keyframe_selected = self.keyframe_tree.selection()
        if not keyframe_selected:
            messagebox.showwarning("警告", "请先选择要删除的关键帧")
            return
            
        # 从tags中获取原始帧数（避免浮点数精度问题）
        tags = self.keyframe_tree.item(keyframe_selected[0])['tags']
        if tags and len(tags) > 0:
            frame = int(tags[0])
        else:
            # 兼容旧数据：如果没有tags，使用秒数计算
            values = self.keyframe_tree.item(keyframe_selected[0])['values']
            seconds = float(values[0].rstrip('秒'))
            frame = int(seconds * self.fps)
        
        # 获取秒数用于显示
        seconds = frame / self.fps
        
        # 保存历史记录
        self.save_state_to_history(f"删除关键帧 ({current_item['name']} @ {seconds:.1f}秒)")
        
        # 删除关键帧（检查帧是否存在）
        if frame in current_item["keyframes"]:
            current_item["keyframes"].remove(frame)
        else:
            messagebox.showerror("错误", f"关键帧 {seconds:.1f}秒 不存在于列表中")
            return
        
        # 更新中间帧插值
        self.update_intermediate_frames(current_item)
        
        # 更新显示
        self.on_keyframe_list_select(None)
        
        # 记录日志
        self.log(f"✓ 删除关键帧: {current_item['name']} @ {seconds}秒", 'success')
        
    def update_stage_preview(self):
        self.ax.clear()
        
        # 计算不可见区域宽度（所有情况下都需要）
        invisible_width = self.stage_width / 8  # 左右备台区域宽度为舞台宽度的1/8
        
        # 如果正在播放且有固定视图范围，使用固定范围
        min_y = 0

        if self.is_playing and self.fixed_view_range:
            xlim = self.fixed_view_range['xlim']
            ylim = self.fixed_view_range['ylim']
            # 直接使用捕获的固定范围，不要再次应用缩放
            # （捕获时已经包含了缩放和平移的效果）
            self.ax.set_xlim(xlim)
            self.ax.set_ylim(ylim)
            min_y = float(ylim[0])  # 保证min_y有值
            # 设置固定的长宽比
            self.ax.set_aspect('equal', adjustable='datalim')
        else:
            # 动态计算视图范围
            waiting_actors = self.get_waiting_area_actors()
            waiting_props = self.get_waiting_area_props()
            for actor in waiting_actors:
                for pos in actor["positions"]:
                    min_y = min(min_y, pos[1] - actor["size"])
            for prop in waiting_props:
                for pos in prop["positions"]:
                    min_y = min(min_y, pos[1] - max(prop["width"], prop["height"])/2)
            min_audience_height = self.calculate_minimum_audience_height()
            min_y = min(min_y, -min_audience_height)
            if waiting_actors or waiting_props or len(self.actors) > 0 or len(self.props) > 0:
                min_y -= 1.0
            
            # 计算基础视图范围
            base_x_min = -self.stage_width/2 - invisible_width
            base_x_max = self.stage_width/2 + invisible_width
            backstage_height = self.stage_height / 8
            base_y_min = min_y
            base_y_max = self.stage_height + backstage_height + 1
            
            # 计算视图中心（如果有自定义中心则使用，否则使用默认中心）
            if self.view_center is not None:
                x_center, y_center = self.view_center
            else:
                x_center = (base_x_min + base_x_max) / 2
                y_center = (base_y_min + base_y_max) / 2
            
            # 应用缩放（以视图中心为缩放中心）
            x_range = (base_x_max - base_x_min) / self.zoom_scale
            y_range = (base_y_max - base_y_min) / self.zoom_scale
            
            self.ax.set_xlim(x_center - x_range/2, x_center + x_range/2)
            self.ax.set_ylim(y_center - y_range/2, y_center + y_range/2)
        
        # 设置固定的长宽比，确保舞台和对象不会变形
        # 使用 'datalim' 让坐标轴可以调整大小，同时保持数据的长宽比
        self.ax.set_aspect('equal', adjustable='datalim')
        
        # 绘制舞台边界
        stage_rect = Rectangle((-self.stage_width/2, 0), self.stage_width, self.stage_height, 
                             fill=False, color='black', linewidth=2)
        self.ax.add_patch(stage_rect)
        
        # 绘制舞台中线（红色虚线，从底部到顶部）
        self.ax.plot([0, 0], [0, self.stage_height], 'r--', linewidth=0.8, alpha=0.5, label='中线')
        
        # 绘制舞台区域标记
        self.ax.axhline(y=0, color='gray', linestyle='--', alpha=0.5)  # 添加舞台边界线
        self.ax.axhline(y=self.stage_height, color='gray', linestyle='--', alpha=0.5)  # 添加舞台顶部边界线
        self.ax.axvline(x=-self.stage_width/2, color='gray', linestyle='--', alpha=0.5)  # 添加左侧边界线
        self.ax.axvline(x=self.stage_width/2, color='gray', linestyle='--', alpha=0.5)  # 添加右侧边界线
        
        # 绘制不可见区域标识
        # 左侧不可见区域
        left_invisible = Rectangle((-self.stage_width/2 - invisible_width, 0), 
                                 invisible_width, self.stage_height,
                                 fill=True, color='gray', alpha=0.3)
        self.ax.add_patch(left_invisible)
        self.ax.text(-self.stage_width/2 - invisible_width/2, self.stage_height/2, '左侧\n备台区域', 
                     rotation=90, ha='center', va='center', color='gray', alpha=0.7, fontsize=12)
        
        # 右侧不可见区域
        right_invisible = Rectangle((self.stage_width/2, 0), 
                                  invisible_width, self.stage_height,
                                  fill=True, color='gray', alpha=0.3)
        self.ax.add_patch(right_invisible)
        self.ax.text(self.stage_width/2 + invisible_width/2, self.stage_height/2, '右侧\n备台区域', 
                     rotation=90, ha='center', va='center', color='gray', alpha=0.7, fontsize=12)
        
        # 后方备台区域 - 在舞台上方增加一个备台区域，连接左右两侧
        backstage_height = self.stage_height / 8  # 后方备台区域高度为舞台高度的1/8
        # 扩展后方备台区域，覆盖整个宽度包括左右两侧
        upper_backstage = Rectangle((-self.stage_width/2 - invisible_width, self.stage_height), 
                                   self.stage_width + 2 * invisible_width, backstage_height,
                                   fill=True, color='gray', alpha=0.3)
        self.ax.add_patch(upper_backstage)
        self.ax.text(0, self.stage_height + backstage_height/2, '后方备台区域', 
                     ha='center', va='center', color='gray', alpha=0.7, fontsize=12)
        
        # 添加区域标识 - 根据实际内容调整位置
        if min_y < 0:
            self.ax.text(0, min_y/2, '观众区域', ha='center', va='center', color='gray', alpha=0.7)
        
        # 绘制所有演员
        for actor in self.actors:
            # 获取当前位置
            if actor["keyframes"]:  # 如果有关键帧
                # 找到当前帧之前和之后的关键帧
                prev_frame = max([f for f in actor["keyframes"] if f <= self.current_frame], default=None)
                next_frame = min([f for f in actor["keyframes"] if f > self.current_frame], default=None)
                
                if prev_frame is not None:
                    if next_frame is not None:
                        # 在两个关键帧之间进行插值
                        pos = actor["positions"][self.current_frame]
                    else:
                        # 使用最后一个关键帧的位置
                        pos = actor["positions"][prev_frame]
                else:
                    # 使用初始位置
                    pos = actor["positions"][0]
            else:
                # 没有关键帧时使用初始位置
                pos = actor["positions"][0]
            
            # 检查是否有临时位置覆盖
            actor_id = self.get_element_id(actor)
            if actor_id in self.temp_position_overrides:
                pos = self.temp_position_overrides[actor_id]
            
            # 获取颜色，如果没有颜色属性则使用默认颜色
            color = actor.get("color", "blue")
            # 获取字号，如果没有字号属性则使用默认字号
            font_size = actor.get("font_size", 10)
            
            # 绘制演员
            if actor["shape"] == "circle":
                circle = Circle((pos[0], pos[1]), actor["size"], 
                             fill=False,  # 改为非填充
                             color=color, 
                             linewidth=2)
                self.ax.add_patch(circle)
                self.ax.text(pos[0], pos[1], actor["name"], 
                           ha='center', va='center', 
                           color=color,  # 文字颜色与轮廓一致
                           fontsize=font_size, 
                           weight='bold')
            elif actor["shape"] == "square":
                rect = Rectangle((pos[0]-actor["size"]/2, pos[1]-actor["size"]/2),
                               actor["size"], actor["size"], 
                               fill=False,  # 改为非填充
                               color=color, 
                               linewidth=2)
                self.ax.add_patch(rect)
                self.ax.text(pos[0], pos[1], actor["name"], 
                           ha='center', va='center', 
                           color=color,  # 文字颜色与轮廓一致
                           fontsize=font_size, 
                           weight='bold')
            elif actor["shape"] == "triangle":
                triangle = Polygon([(pos[0], pos[1]+actor["size"]),
                                  (pos[0]-actor["size"], pos[1]-actor["size"]),
                                  (pos[0]+actor["size"], pos[1]-actor["size"])], 
                                 fill=False,  # 改为非填充
                                 color=color, 
                                 linewidth=2)
                self.ax.add_patch(triangle)
                self.ax.text(pos[0], pos[1], actor["name"], 
                           ha='center', va='center', 
                           color=color,  # 文字颜色与轮廓一致
                           fontsize=font_size, 
                           weight='bold')
        
        # 绘制所有道具
        for prop in self.props:
            # 获取当前位置
            if prop["keyframes"]:  # 如果有关键帧
                # 找到当前帧之前和之后的关键帧
                prev_frame = max([f for f in prop["keyframes"] if f <= self.current_frame], default=None)
                next_frame = min([f for f in prop["keyframes"] if f > self.current_frame], default=None)
                
                if prev_frame is not None:
                    if next_frame is not None:
                        # 在两个关键帧之间进行插值
                        pos = prop["positions"][self.current_frame]
                    else:
                        # 使用最后一个关键帧的位置
                        pos = prop["positions"][prev_frame]
                else:
                    pos = prop["positions"][0]
            else:
                pos = prop["positions"][0]
            
            # 检查是否有临时位置覆盖
            prop_id = self.get_element_id(prop)
            if prop_id in self.temp_position_overrides:
                pos = self.temp_position_overrides[prop_id]
                
            # 获取颜色，如果没有颜色属性则使用默认颜色
            color = prop.get("color", "red")
            # 获取字号，如果没有字号属性则使用默认字号
            font_size = prop.get("font_size", 10)
                
            if prop["shape"] == "rectangle":
                rect = Rectangle((pos[0]-prop["width"]/2, pos[1]-prop["height"]/2),
                               prop["width"], prop["height"], 
                               fill=False,  # 改为非填充
                               color=color, 
                               linewidth=2)
                self.ax.add_patch(rect)
                self.ax.text(pos[0], pos[1], prop["name"], 
                           ha='center', va='center', 
                           color=color,  # 文字颜色与轮廓一致
                           fontsize=font_size, 
                           weight='bold')
            elif prop["shape"] == "circle":
                circle = Circle((pos[0], pos[1]), prop["width"]/2, 
                             fill=False,  # 改为非填充
                             color=color, 
                             linewidth=2)
                self.ax.add_patch(circle)
                self.ax.text(pos[0], pos[1], prop["name"], 
                           ha='center', va='center', 
                           color=color,  # 文字颜色与轮廓一致
                           fontsize=font_size, 
                           weight='bold')
            elif prop["shape"] == "triangle":
                triangle = Polygon([(pos[0], pos[1]+prop["height"]/2),
                                  (pos[0]-prop["width"]/2, pos[1]-prop["height"]/2),
                                  (pos[0]+prop["width"]/2, pos[1]-prop["height"]/2)], 
                                 fill=False,  # 改为非填充
                                 color=color, 
                                 linewidth=2)
                self.ax.add_patch(triangle)
                self.ax.text(pos[0], pos[1], prop["name"], 
                           ha='center', va='center', 
                           color=color,  # 文字颜色与轮廓一致
                           fontsize=font_size, 
                           weight='bold')
        
        # 绘制文本框 - 使用整秒对应的帧，确保不超出范围
        current_second_frame = int(self.current_second) * self.fps
        # 确保索引不超出范围，添加额外的安全检查
        if (current_second_frame < len(self.text_box["contents"]) and 
            current_second_frame >= 0 and 
            len(self.text_box["contents"]) > 0):
            text_content = self.text_box["contents"][current_second_frame]
        else:
            text_content = ""  # 如果超出范围，显示空文本
        
        # 绘制文本框 - 放置在后方备台区域上方且不重合
        backstage_height = self.stage_height / 8  # 后方备台区域高度
        text_y_position = self.stage_height + backstage_height + 0.5  # 在后方备台区域上方0.5单位
        self.ax.text(0, text_y_position,
                    text_content,
                    ha='center', va='center',
                    fontsize=self.text_box["font_size"],
                    color='black',
                    bbox=dict(facecolor='white', alpha=0.7, edgecolor='black', pad=5))  # 增加内边距
        
        # 设置坐标轴标签（只在舞台区域显示）
        self.ax.set_xlabel('X', fontsize=8)
        self.ax.set_ylabel('Y', fontsize=8)
        
        # 设置标题 - 减小pad值，避免标题过于上移
        self.ax.set_title(f'当前时间: {self.current_second:.1f}秒', fontsize=12, pad=5)
        
        # 自定义刻度格式化函数
        def format_func(value, pos):
            if value.is_integer():
                return f'{int(value)}'
            else:
                return f'{value:.1f}'
        
        # 设置刻度格式
        self.ax.xaxis.set_major_formatter(FuncFormatter(format_func))
        self.ax.yaxis.set_major_formatter(FuncFormatter(format_func))
        
        # 固定坐标轴刻度范围，避免播放时变化
        # 计算合适的刻度范围（只显示舞台区域的刻度）
        # X轴刻度：根据舞台宽度设置
        x_tick_spacing = max(2, int(self.stage_width / 5))  # 大约5个刻度
        x_ticks = np.arange(-self.stage_width/2, self.stage_width/2 + 1, x_tick_spacing)
        self.ax.set_xticks(x_ticks)
        
        # Y轴刻度：只显示舞台内的刻度（0到stage_height）
        y_tick_spacing = max(2, int(self.stage_height / 5))  # 大约5个刻度
        y_ticks = np.arange(0, self.stage_height + 1, y_tick_spacing)
        self.ax.set_yticks(y_ticks)
        
        # 设置X轴刻度位置在Y=0线
        self.ax.xaxis.set_ticks_position('bottom')
        self.ax.xaxis.set_label_position('bottom')
        self.ax.spines['bottom'].set_position(('data', 0))
        
        # 只在舞台区域显示网格
        self.ax.grid(True, which='major', axis='both', alpha=0.3)
        
        # 完全隐藏坐标轴边框（spines）
        self.ax.spines['left'].set_visible(False)
        self.ax.spines['right'].set_visible(False)
        self.ax.spines['top'].set_visible(False)
        self.ax.spines['bottom'].set_visible(True)  # 只保留底部坐标轴
        
        # 隐藏Y轴刻度标签（如果不想显示Y轴的数字）
        # 如果想完全隐藏非舞台区域的坐标轴显示，可以设置：
        # self.ax.yaxis.set_visible(False)  # 完全隐藏Y轴
        # 或者只显示舞台区域内的Y轴标签：
        self.ax.tick_params(axis='y', which='both', left=False, right=False)  # 隐藏Y轴刻度线
        
        # 调整布局以适应容器大小
        # 注意：避免在每次更新时调用 tight_layout，因为可能导致窗口移动
        # 只在必要时调用（如窗口大小改变时）
        # try:
        #     self.fig.tight_layout(pad=0.5)
        # except:
        #     pass  # 如果 tight_layout 失败，忽略错误继续
        
        # 使用 draw_idle() 而不是 draw()，避免阻塞音频播放
        # draw_idle() 会在下一个空闲周期绘制，不会立即阻塞主线程
        self.canvas.draw_idle()

    def calculate_layout_parameters(self):
        """计算布局参数"""
        # 观众区域位置（舞台下方）
        audience_start_y = -1.5  # 观众区域起始位置
        
        # 基础参数
        min_spacing = 0.8  # 最小间距
        max_elements_per_row = max(1, int((self.stage_width - 1) / min_spacing))  # 每行最大元素数
        
        return {
            'audience_start_y': audience_start_y,
            'min_spacing': min_spacing,
            'max_elements_per_row': max_elements_per_row,
            'stage_width': self.stage_width
        }
    
    def get_waiting_area_actors(self):
        """获取在等候区域的演员（当前帧位置在观众区域的演员）"""
        params = self.calculate_layout_parameters()
        waiting_actors = []
        for actor in self.actors:
            current_pos = actor["positions"][self.current_frame]
            if current_pos[1] <= params['audience_start_y']:
                waiting_actors.append(actor)
        return waiting_actors
    
    def get_waiting_area_props(self):
        """获取在等候区域的道具（当前帧位置在观众区域的道具）"""
        params = self.calculate_layout_parameters()
        waiting_props = []
        for prop in self.props:
            current_pos = prop["positions"][self.current_frame]
            if current_pos[1] <= params['audience_start_y']:
                waiting_props.append(prop)
        return waiting_props

    def calculate_element_size(self, element, element_type):
        """计算元素的实际占用空间"""
        if element_type == "actor":
            return element["size"] * 2  # 直径
        else:  # prop
            return max(element["width"], element["height"])
    
    def arrange_waiting_area(self):
        """重新排列等候区域的所有演员和道具"""
        params = self.calculate_layout_parameters()
        waiting_actors = self.get_waiting_area_actors()
        waiting_props = self.get_waiting_area_props()
        
        # 将演员和道具合并，按添加顺序排序
        all_elements = []
        for actor in waiting_actors:
            all_elements.append(('actor', actor))
        for prop in waiting_props:
            all_elements.append(('prop', prop))
        
        if not all_elements:
            return
        
        # 计算布局
        current_x = -self.stage_width / 2 + 0.5  # 从左边开始，留一点边距
        current_y = params['audience_start_y']
        current_row_elements = 0
        max_height_in_row = 0
        
        for element_type, element in all_elements:
            element_size = self.calculate_element_size(element, element_type)
            
            # 检查是否需要换行
            if (current_x + element_size > self.stage_width / 2 - 0.5 or 
                current_row_elements >= params['max_elements_per_row']):
                # 换行
                current_x = -self.stage_width / 2 + 0.5
                current_y -= (max_height_in_row + params['min_spacing'])
                current_row_elements = 0
                max_height_in_row = 0
            
            # 设置位置
            pos_x = current_x + element_size / 2
            pos_y = current_y
            
            # 只为没有关键帧的元素（新添加的元素）设置位置和关键帧
            # 已有关键帧的元素不应被自动修改
            if not element["keyframes"]:
                # 新元素：为所有帧设置相同的初始位置
                for frame in range(self.total_frames):
                    element["positions"][frame] = (pos_x, pos_y)
            
            # 更新布局参数
            current_x += element_size + params['min_spacing']
            current_row_elements += 1
            max_height_in_row = max(max_height_in_row, element_size)
        
        print(f"重新排列了 {len(all_elements)} 个元素在等候区域")
    
    def get_element_id(self, element):
        """获取元素的唯一标识"""
        return f"{element['name']}_{id(element)}"
    
    def convert_temp_keyframe_to_permanent(self, element, frame):
        """将临时关键帧转换为正式关键帧"""
        element_id = self.get_element_id(element)
        temp_key = (element_id, frame)
        
        if temp_key in self.temp_keyframes:
            # 移除临时标记，关键帧变为正式关键帧
            del self.temp_keyframes[temp_key]
            print(f"✓ 临时关键帧转为正式关键帧: {element['name']} 在第 {frame} 帧 (剩余临时关键帧: {len(self.temp_keyframes)})")
            return True
        else:
            print(f"尝试转换临时关键帧失败: {element['name']} 在第 {frame} 帧 (不存在于临时记录中)")
            return False
    
    def cleanup_temp_keyframes_on_time_change(self):
        """当时间改变时清理不再需要的临时关键帧"""
        if not self.temp_keyframes:
            return  # 没有临时关键帧，直接返回
            
        print(f"临时关键帧清理检查 - 当前帧: {self.current_frame}, 临时关键帧数量: {len(self.temp_keyframes)}")
        to_remove = []
        
        for (element_id, frame), _ in self.temp_keyframes.items():
            # 找到对应的元素
            target_element = None
            for actor in self.actors:
                if self.get_element_id(actor) == element_id:
                    target_element = actor
                    break
            if not target_element:
                for prop in self.props:
                    if self.get_element_id(prop) == element_id:
                        target_element = prop
                        break
            
            if target_element and frame in target_element["keyframes"]:
                # 移除临时关键帧
                target_element["keyframes"].remove(frame)
                # 更新插值
                self.update_intermediate_frames(target_element)
                to_remove.append((element_id, frame))
                print(f"✓ 清理临时关键帧: {target_element['name']} 在第 {frame} 帧")
            elif not target_element:
                # 元素已经不存在，也要清理记录
                to_remove.append((element_id, frame))
                print(f"✓ 清理孤立的临时关键帧记录: {element_id} 在第 {frame} 帧")
        
        # 清理临时关键帧记录
        for key in to_remove:
            if key in self.temp_keyframes:
                del self.temp_keyframes[key]
        
        if to_remove:
            print(f"清理完成 - 清理了 {len(to_remove)} 个临时关键帧，剩余: {len(self.temp_keyframes)}")
        
        # 额外验证：检查是否有应该被清理但没有被清理的记录
        remaining_temp = list(self.temp_keyframes.keys())
        if remaining_temp:
            print(f"剩余临时关键帧: {remaining_temp}")
    
    def capture_current_view_range(self):
        """捕获当前视图范围，用于播放期间固定视图"""
        try:
            if hasattr(self, 'ax') and self.ax is not None:
                xlim = self.ax.get_xlim()
                ylim = self.ax.get_ylim()
                self.fixed_view_range = {'xlim': xlim, 'ylim': ylim}
                print(f"捕获视图范围: X={xlim}, Y={ylim}")
            else:
                print("警告: 无法捕获视图范围，ax对象不存在")
                self.fixed_view_range = None
        except Exception as e:
            print(f"捕获视图范围时出错: {e}")
            self.fixed_view_range = None
    
    def calculate_minimum_audience_height(self):
        """计算观众区域的最小高度，确保至少容纳最大元素的1.5倍"""
        max_element_size = 0
        
        # 检查所有演员的大小
        for actor in self.actors:
            if actor["shape"] == "circle":
                element_size = actor["size"] * 2  # 直径
            elif actor["shape"] == "square":
                element_size = actor["size"]
            elif actor["shape"] == "triangle":
                element_size = actor["size"] * 2  # 大概估算
            else:
                element_size = actor.get("size", 1.0)
            max_element_size = max(max_element_size, element_size)
        
        # 检查所有道具的大小
        for prop in self.props:
            element_size = max(prop["width"], prop["height"])
            max_element_size = max(max_element_size, element_size)
        
        # 最小观众区域高度为最大元素的1.5倍，但不少于2.0
        min_height = max(2.0, max_element_size * 1.5)
        print(f"计算最小观众区域高度: 最大元素={max_element_size:.2f}, 最小高度={min_height:.2f}")
        return min_height
    
    def reset_to_waiting_area(self):
        """将选中的演员或道具重置到等候区域"""
        selection = self.keyframe_listbox.curselection()
        if not selection:
            messagebox.showwarning("提示", "请先选择要重置的演员或道具")
            return
        
        # 获取选中的项目
        selected_index = selection[0]
        item_text = self.keyframe_listbox.get(selected_index)
        
        # 解析项目类型和名称
        if item_text.startswith("演员: "):
            item_type = "actor"
            item_name = item_text[4:]  # 去掉"演员: "前缀
            items_list = self.actors
        elif item_text.startswith("道具: "):
            item_type = "prop"
            item_name = item_text[4:]  # 去掉"道具: "前缀
            items_list = self.props
        else:
            messagebox.showerror("错误", "无法识别选中的项目类型")
            return
        
        # 找到对应的演员或道具
        target_item = None
        for item in items_list:
            if item["name"] == item_name:
                target_item = item
                break
        
        if not target_item:
            messagebox.showerror("错误", "找不到对应的演员或道具")
            return
        
        # 计算等候区域的新位置
        params = self.calculate_layout_parameters()
        waiting_actors = self.get_waiting_area_actors()
        waiting_props = self.get_waiting_area_props()
        
        # 计算新位置（在等候区域末尾）
        all_waiting_elements = len(waiting_actors) + len(waiting_props)
        element_size = self.calculate_element_size(target_item, item_type)
        
        # 简单布局：在等候区域从左到右排列
        new_x = -self.stage_width/2 + 0.5 + (all_waiting_elements % params['max_elements_per_row']) * (element_size + params['min_spacing']) + element_size/2
        new_y = params['audience_start_y'] - (all_waiting_elements // params['max_elements_per_row']) * (element_size + params['min_spacing'])
        
        # 设置新位置（根据是否有关键帧决定处理方式）
        if not target_item["keyframes"]:
            # 如果没有关键帧，直接设置所有帧的位置
            for frame in range(self.total_frames):
                target_item["positions"][frame] = (new_x, new_y)
        else:
            # 如果有关键帧，添加临时关键帧
            target_item["positions"][self.current_frame] = (new_x, new_y)
            if self.current_frame not in target_item["keyframes"]:
                target_item["keyframes"].append(self.current_frame)
                target_item["keyframes"].sort()
                # 标记为临时关键帧
                element_id = self.get_element_id(target_item)
                self.temp_keyframes[(element_id, self.current_frame)] = True
                print(f"✓ 添加临时关键帧: {target_item['name']} 在第 {self.current_frame} 帧")
                # 更新插值
                self.update_intermediate_frames(target_item)
        
        # 重新排列等候区域
        self.arrange_waiting_area()
        
        # 更新显示
        self.update_stage_preview()
        self.on_keyframe_list_select(None)  # 刷新关键帧列表
        
        print(f"已将 {item_name} 重置到等候区域")
    
    def reset_all_to_waiting_area(self):
        """将所有演员和道具重置到等候区域"""
        # 确认对话框
        result = messagebox.askyesno(
            "确认操作", 
            "确定要将所有演员和道具重置到等候区域吗？\n\n注意：重置时不会在当前时间点添加关键帧，但当你移动元素时，关键帧将被正确添加。",
            icon='question'
        )
        
        if not result:
            return
        
        # 计算布局参数
        params = self.calculate_layout_parameters()
        
        # 获取所有演员和道具
        all_actors = self.actors.copy()
        all_props = self.props.copy()
        
        if not all_actors and not all_props:
            messagebox.showinfo("提示", "当前没有演员或道具需要重置")
            return
        
        # 将所有元素合并进行统一布局
        all_elements = []
        for actor in all_actors:
            all_elements.append(('actor', actor))
        for prop in all_props:
            all_elements.append(('prop', prop))
        
        # 计算布局
        current_x = -self.stage_width / 2 + 0.5  # 从左边开始，留一点边距
        current_y = params['audience_start_y']
        current_row_elements = 0
        max_height_in_row = 0
        keyframe_added_count = 0
        
        for element_type, element in all_elements:
            element_size = self.calculate_element_size(element, element_type)
            
            # 检查是否需要换行
            if (current_x + element_size > self.stage_width / 2 - 0.5 or 
                current_row_elements >= params['max_elements_per_row']):
                # 换行
                current_x = -self.stage_width / 2 + 0.5
                current_y -= (max_height_in_row + params['min_spacing'])
                current_row_elements = 0
                max_height_in_row = 0
            
            # 设置位置
            pos_x = current_x + element_size / 2
            pos_y = current_y
            
            # 更新位置（根据是否有关键帧和当前时间决定处理方式）
            if not element["keyframes"]:
                # 如果没有关键帧，无论在什么时间点，都只移动位置，不设定关键帧
                for frame in range(self.total_frames):
                    element["positions"][frame] = (pos_x, pos_y)
            elif self.current_frame == 0:
                # 如果在第0帧且有关键帧，使用临时位置覆盖机制
                # 不修改实际的positions数组，而是记录临时位置覆盖
                element_id = self.get_element_id(element)
                if not hasattr(self, 'temp_position_overrides'):
                    self.temp_position_overrides = {}
                self.temp_position_overrides[element_id] = (pos_x, pos_y)
                print(f"✓ 批量重置 - 在0秒重置: {element['name']} 设置临时位置覆盖，不修改关键帧")
            else:
                # 如果有关键帧且不在第0帧，添加临时关键帧
                element["positions"][self.current_frame] = (pos_x, pos_y)
                if self.current_frame not in element["keyframes"]:
                    element["keyframes"].append(self.current_frame)
                    element["keyframes"].sort()
                    keyframe_added_count += 1
                    # 标记为临时关键帧
                    element_id = self.get_element_id(element)
                    self.temp_keyframes[(element_id, self.current_frame)] = True
                    print(f"✓ 批量重置 - 添加临时关键帧: {element['name']} 在第 {self.current_frame} 帧")
                    # 更新插值
                    self.update_intermediate_frames(element)
            
            # 更新布局参数
            current_x += element_size + params['min_spacing']
            current_row_elements += 1
            max_height_in_row = max(max_height_in_row, element_size)
        
        # 更新显示
        self.update_stage_preview()
        self.on_keyframe_list_select(None)  # 刷新关键帧列表
        
        print(f"全部重置完成：{len(all_elements)} 个元素，{keyframe_added_count} 个新关键帧")

    def add_actor(self):
        """添加演员"""
        try:
            # 获取演员名称
            name = self.actor_name_entry.get()
            if not name:
                raise ValueError("演员名称不能为空")
            
            # 获取演员大小
            try:
                size = float(self.actor_size_entry.get())
                if size <= 0:
                    raise ValueError
            except ValueError:
                raise ValueError("演员大小必须是大于0的数字")
                
            # 获取字号
            try:
                font_size = float(self.actor_font_size.get())
                if font_size <= 0:
                    raise ValueError
            except ValueError:
                raise ValueError("字号必须是大于0的数字")
            
            # 获取颜色（使用映射后的英文颜色值）
            color = self.color_map[self.actor_color_var.get()]
            
            # 临时位置，稍后会通过arrange_waiting_area重新计算
            temp_pos = (0, -1.5)
            
            # 创建演员对象
            actor = {
                "name": name,
                "shape": self.actor_shape_var.get(),
                "size": size,
                "color": color,  # 使用映射后的颜色
                "font_size": font_size,
                "positions": [temp_pos for _ in range(self.total_frames)],
                "keyframes": []  # 不自动创建关键帧
            }
            
            # 保存历史记录
            self.save_state_to_history(f"添加演员 ({name})")
            
            self.actors.append(actor)
            
            # 重新排列等候区域
            self.arrange_waiting_area()
            
            # 更新右侧关键帧列表 - 插入到所有演员的后面、所有道具的前面
            # 索引位置应该是当前演员总数-1（因为刚刚append了新演员）
            insert_position = len(self.actors) - 1
            self.keyframe_listbox.insert(insert_position, f"演员: {actor['name']}")
            
            # 只清空名称输入框，保留其他设置
            self.actor_name_entry.delete(0, tk.END)
            
            # 更新显示
            self.update_stage_preview()
            
            # 记录日志
            self.log(f"✓ 添加演员: {name}", 'success')
            
        except ValueError as e:
            messagebox.showerror("错误", str(e))

    def add_prop(self):
        """添加道具"""
        try:
            # 获取道具名称
            name = self.prop_name_entry.get()
            if not name:
                raise ValueError("道具名称不能为空")
            
            # 获取道具宽度
            try:
                width = float(self.prop_width_entry.get())
                if width <= 0:
                    raise ValueError
            except ValueError:
                raise ValueError("道具宽度必须是大于0的数字")
                
            # 获取道具高度
            try:
                height = float(self.prop_height_entry.get())
                if height <= 0:
                    raise ValueError
            except ValueError:
                raise ValueError("道具高度必须是大于0的数字")
                
            # 获取字号
            try:
                font_size = float(self.prop_font_size.get())
                if font_size <= 0:
                    raise ValueError
            except ValueError:
                raise ValueError("字号必须是大于0的数字")
            
            # 获取颜色（使用映射后的英文颜色值）
            color = self.color_map[self.prop_color_var.get()]
            
            # 临时位置，稍后会通过arrange_waiting_area重新计算
            temp_pos = (0, -1.5)
            
            # 创建道具对象
            prop = {
                "name": name,
                "shape": self.prop_shape_var.get(),
                "width": width,
                "height": height,
                "color": color,  # 使用映射后的颜色
                "font_size": font_size,
                "positions": [temp_pos for _ in range(self.total_frames)],
                "keyframes": []  # 不自动创建关键帧
            }
            
            # 保存历史记录
            self.save_state_to_history(f"添加道具 ({name})")
            
            self.props.append(prop)
            
            # 重新排列等候区域
            self.arrange_waiting_area()
            
            # 更新右侧关键帧列表
            self.keyframe_listbox.insert(tk.END, f"道具: {prop['name']}")
            
            # 只清空名称输入框，保留其他设置
            self.prop_name_entry.delete(0, tk.END)
            
            # 更新显示
            self.update_stage_preview()
            
            # 记录日志
            self.log(f"✓ 添加道具: {name}", 'success')
            
        except ValueError as e:
            messagebox.showerror("错误", str(e))

    def update_intermediate_frames(self, item):
        """更新两个关键帧之间的中间帧位置，使用线性插值确保匀速移动"""
        if len(item["keyframes"]) < 2:
            return
            
        # 按时间排序关键帧
        sorted_frames = sorted(item["keyframes"])
        
        # 更新每对关键帧之间的中间帧
        for i in range(len(sorted_frames) - 1):
            start_frame = sorted_frames[i]
            end_frame = sorted_frames[i + 1]
            start_pos = item["positions"][start_frame]
            end_pos = item["positions"][end_frame]
            
            # 计算总距离
            total_frames = end_frame - start_frame
            if total_frames <= 1:
                continue
                
            # 计算每帧的移动距离
            dx = (end_pos[0] - start_pos[0]) / total_frames
            dy = (end_pos[1] - start_pos[1]) / total_frames
            
            # 使用线性插值更新中间帧位置
            for frame in range(start_frame + 1, end_frame):
                progress = frame - start_frame
                x = start_pos[0] + dx * progress
                y = start_pos[1] + dy * progress
                item["positions"][frame] = (x, y)

    def on_mouse_press(self, event):
        """处理鼠标按下事件"""
        if event.inaxes != self.ax:
            return
            
        # 获取鼠标点击位置
        x, y = event.xdata, event.ydata
        
        # 右键（button==3）或中键（button==2）用于平移视图
        if event.button == 3 or event.button == 2:
            # 双击右键重置视图
            if event.dblclick:
                self.view_center = None
                self.zoom_scale = 1.0
                self.update_stage_preview()
                print("🔄 视图已重置到默认状态")
                self.log("🔄 视图已重置", 'info')
                return
            
            # 单击右键开始平移
            self.pan_active = True
            self.pan_start = (x, y)
            # 保存当前视图中心
            xlim = self.ax.get_xlim()
            ylim = self.ax.get_ylim()
            if self.view_center is None:
                self.view_center = ((xlim[0] + xlim[1]) / 2, (ylim[0] + ylim[1]) / 2)
            print(f"🖐️ 开始平移视图，起始位置: ({x:.2f}, {y:.2f})")
            return  # 平移模式下不处理对象拖动
        
        # 检查是否点击了演员
        for i, actor in enumerate(self.actors):
            # 获取当前位置
            if actor["keyframes"]:  # 如果有关键帧
                # 找到当前帧之前和之后的关键帧
                prev_frame = max([f for f in actor["keyframes"] if f <= self.current_frame], default=None)
                next_frame = min([f for f in actor["keyframes"] if f > self.current_frame], default=None)
                
                if prev_frame is not None:
                    if next_frame is not None:
                        # 在两个关键帧之间进行插值
                        pos = actor["positions"][self.current_frame]
                    else:
                        # 使用最后一个关键帧的位置
                        pos = actor["positions"][prev_frame]
                else:
                    # 使用初始位置
                    pos = actor["positions"][0]
            else:
                # 没有关键帧时使用初始位置
                pos = actor["positions"][0]
            
            # 检查是否有临时位置覆盖
            actor_id = self.get_element_id(actor)
            if actor_id in self.temp_position_overrides:
                pos = self.temp_position_overrides[actor_id]
            
            # 检查点击，计算偏移量
            if actor["shape"] == "circle":
                if ((x - pos[0])**2 + (y - pos[1])**2) <= actor["size"]**2:
                    self.dragging = True
                    self.drag_item = actor
                    self.drag_type = "actor"
                    self.drag_index = i
                    # 记录鼠标点击位置与元素中心的偏移量
                    self.drag_offset = (x - pos[0], y - pos[1])
                    self.drag_start_pos = pos  # 记录元素的起始位置
                    
                    # 清除临时位置覆盖（开始拖动时）
                    if actor_id in self.temp_position_overrides:
                        self.temp_position_overrides.pop(actor_id)
                    
                    # 将当前帧的临时关键帧转为正式关键帧
                    self.convert_temp_keyframe_to_permanent(actor, self.current_frame)
                    
                    # 选中对应的列表项
                    self.keyframe_listbox.selection_clear(0, tk.END)
                    self.keyframe_listbox.selection_set(i)
                    self.keyframe_listbox.see(i)
                    # 更新关键帧表格
                    self.on_keyframe_list_select(None)
                    break
            elif actor["shape"] == "square":
                if (abs(x - pos[0]) <= actor["size"]/2 and 
                    abs(y - pos[1]) <= actor["size"]/2):
                    self.dragging = True
                    self.drag_item = actor
                    self.drag_type = "actor"
                    self.drag_index = i
                    # 记录鼠标点击位置与元素中心的偏移量
                    self.drag_offset = (x - pos[0], y - pos[1])
                    self.drag_start_pos = pos  # 记录元素的起始位置
                    
                    # 清除临时位置覆盖（开始拖动时）
                    if actor_id in self.temp_position_overrides:
                        self.temp_position_overrides.pop(actor_id)
                    
                    # 将当前帧的临时关键帧转为正式关键帧
                    self.convert_temp_keyframe_to_permanent(actor, self.current_frame)
                    
                    # 选中对应的列表项
                    self.keyframe_listbox.selection_clear(0, tk.END)
                    self.keyframe_listbox.selection_set(i)
                    self.keyframe_listbox.see(i)
                    # 更新关键帧表格
                    self.on_keyframe_list_select(None)
                    break
            elif actor["shape"] == "triangle":
                # 简化的三角形碰撞检测
                if (abs(x - pos[0]) <= actor["size"] and 
                    abs(y - pos[1]) <= actor["size"]):
                    self.dragging = True
                    self.drag_item = actor
                    self.drag_type = "actor"
                    self.drag_index = i
                    # 记录鼠标点击位置与元素中心的偏移量
                    self.drag_offset = (x - pos[0], y - pos[1])
                    self.drag_start_pos = pos  # 记录元素的起始位置
                    
                    # 清除临时位置覆盖（开始拖动时）
                    if actor_id in self.temp_position_overrides:
                        self.temp_position_overrides.pop(actor_id)
                    
                    # 将当前帧的临时关键帧转为正式关键帧
                    self.convert_temp_keyframe_to_permanent(actor, self.current_frame)
                    
                    # 选中对应的列表项
                    self.keyframe_listbox.selection_clear(0, tk.END)
                    self.keyframe_listbox.selection_set(i)
                    self.keyframe_listbox.see(i)
                    # 更新关键帧表格
                    self.on_keyframe_list_select(None)
                    break
                    
        # 如果没有选中演员，检查是否点击了道具
        if not self.dragging:
            for i, prop in enumerate(self.props):
                # 获取当前位置
                if prop["keyframes"]:  # 如果有关键帧
                    # 找到当前帧之前和之后的关键帧
                    prev_frame = max([f for f in prop["keyframes"] if f <= self.current_frame], default=None)
                    next_frame = min([f for f in prop["keyframes"] if f > self.current_frame], default=None)
                    
                    if prev_frame is not None:
                        if next_frame is not None:
                            # 在两个关键帧之间进行插值
                            pos = prop["positions"][self.current_frame]
                        else:
                            # 使用最后一个关键帧的位置
                            pos = prop["positions"][prev_frame]
                    else:
                        # 使用初始位置
                        pos = prop["positions"][0]
                else:
                    # 没有关键帧时使用初始位置
                    pos = prop["positions"][0]
                
                # 检查是否有临时位置覆盖
                prop_id = self.get_element_id(prop)
                if prop_id in self.temp_position_overrides:
                    pos = self.temp_position_overrides[prop_id]
                    
                if prop["shape"] == "rectangle":
                    if (abs(x - pos[0]) <= prop["width"]/2 and 
                        abs(y - pos[1]) <= prop["height"]/2):
                        self.dragging = True
                        self.drag_item = prop
                        self.drag_type = "prop"
                        self.drag_index = i
                        # 记录鼠标点击位置与元素中心的偏移量
                        self.drag_offset = (x - pos[0], y - pos[1])
                        self.drag_start_pos = pos  # 记录元素的起始位置
                        
                        # 清除临时位置覆盖（开始拖动时）
                        if prop_id in self.temp_position_overrides:
                            self.temp_position_overrides.pop(prop_id)
                        
                        # 将当前帧的临时关键帧转为正式关键帧
                        self.convert_temp_keyframe_to_permanent(prop, self.current_frame)
                        
                        # 选中对应的列表项
                        self.keyframe_listbox.selection_clear(0, tk.END)
                        self.keyframe_listbox.selection_set(i + len(self.actors))
                        self.keyframe_listbox.see(i + len(self.actors))
                        # 更新关键帧表格
                        self.on_keyframe_list_select(None)
                        break
                elif prop["shape"] == "circle":
                    if ((x - pos[0])**2 + (y - pos[1])**2) <= (prop["width"]/2)**2:
                        self.dragging = True
                        self.drag_item = prop
                        self.drag_type = "prop"
                        self.drag_index = i
                        # 记录鼠标点击位置与元素中心的偏移量
                        self.drag_offset = (x - pos[0], y - pos[1])
                        self.drag_start_pos = pos  # 记录元素的起始位置
                        
                        # 清除临时位置覆盖（开始拖动时）
                        if prop_id in self.temp_position_overrides:
                            self.temp_position_overrides.pop(prop_id)
                        
                        # 将当前帧的临时关键帧转为正式关键帧
                        self.convert_temp_keyframe_to_permanent(prop, self.current_frame)
                        
                        # 选中对应的列表项
                        self.keyframe_listbox.selection_clear(0, tk.END)
                        self.keyframe_listbox.selection_set(i + len(self.actors))
                        self.keyframe_listbox.see(i + len(self.actors))
                        # 更新关键帧表格
                        self.on_keyframe_list_select(None)
                        break
                elif prop["shape"] == "triangle":
                    # 简化的三角形碰撞检测
                    if (abs(x - pos[0]) <= prop["width"]/2 and 
                        abs(y - pos[1]) <= prop["height"]/2):
                        self.dragging = True
                        self.drag_item = prop
                        self.drag_type = "prop"
                        self.drag_index = i
                        # 记录鼠标点击位置与元素中心的偏移量
                        self.drag_offset = (x - pos[0], y - pos[1])
                        self.drag_start_pos = pos  # 记录元素的起始位置
                        
                        # 清除临时位置覆盖（开始拖动时）
                        if prop_id in self.temp_position_overrides:
                            self.temp_position_overrides.pop(prop_id)
                        
                        # 将当前帧的临时关键帧转为正式关键帧
                        self.convert_temp_keyframe_to_permanent(prop, self.current_frame)
                        
                        # 选中对应的列表项
                        self.keyframe_listbox.selection_clear(0, tk.END)
                        self.keyframe_listbox.selection_set(i + len(self.actors))
                        self.keyframe_listbox.see(i + len(self.actors))
                        # 更新关键帧表格
                        self.on_keyframe_list_select(None)
                        break

    def on_mouse_move(self, event):
        """处理鼠标移动事件"""
        # 处理视图平移
        if self.pan_active and self.pan_start is not None:
            if event.inaxes != self.ax or event.xdata is None or event.ydata is None:
                return
            
            # 计算鼠标移动的距离
            dx = event.xdata - self.pan_start[0]
            dy = event.ydata - self.pan_start[1]
            
            # 更新视图中心（反向移动，因为是拖动背景）
            current_center = self.view_center if self.view_center is not None else (0, self.stage_height / 2)
            self.view_center = (current_center[0] - dx, current_center[1] - dy)
            
            # 更新起始位置为当前位置（相对于新的视图中心）
            self.pan_start = (event.xdata, event.ydata)
            
            # 刷新显示
            self.update_stage_preview()
            return
        
        # 处理对象拖动
        if not self.dragging or event.inaxes != self.ax:
            return
        
        # 类型检查：确保拖动相关对象不为None
        if self.drag_item is None or self.drag_offset is None:
            return
            
        # 获取鼠标位置
        x = event.xdata
        y = event.ydata
        
        # 确保鼠标位置有效
        if x is None or y is None:
            return
        
        # 如果是第一次拖动（还未保存过历史），保存历史记录
        if not hasattr(self, '_drag_history_saved') or not self._drag_history_saved:
            self.save_state_to_history(f"拖动对象 ({self.drag_item['name']})")
            self._drag_history_saved = True
        
        # 根据偏移量计算元素的新位置
        new_x = x - self.drag_offset[0]
        new_y = y - self.drag_offset[1]
        
        # 更新位置
        self.drag_item["positions"][self.current_frame] = (new_x, new_y)
        
        # 如果当前帧不是关键帧，添加为关键帧
        if self.current_frame not in self.drag_item["keyframes"]:
            self.drag_item["keyframes"].append(self.current_frame)
            self.drag_item["keyframes"].sort()
        
        # 更新关键帧表格
        self.on_keyframe_list_select(None)
        
        # 更新显示
        self.update_stage_preview()
        
    def on_mouse_release(self, event):
        """处理鼠标释放事件"""
        # 结束视图平移
        if self.pan_active:
            self.pan_active = False
            self.pan_start = None
            print(f"🖐️ 视图平移结束，新中心: ({self.view_center[0]:.2f}, {self.view_center[1]:.2f})" if self.view_center else "🖐️ 视图平移结束")
            return
        
        if not self.dragging:
            return
            
        # 获取最终位置
        if event.inaxes == self.ax:
            x = event.xdata
            y = event.ydata
            self.drag_end_pos = (x, y)
        else:
            # 如果释放时鼠标在预览区域外，将元素限制在预览区域边缘
            # 获取当前预览区域的边界
            x_min, x_max = self.ax.get_xlim()
            y_min, y_max = self.ax.get_ylim()
            
            # 获取鼠标在窗口中的位置（像素坐标）
            if hasattr(event, 'x') and hasattr(event, 'y'):
                # 将像素坐标转换为数据坐标的近似值
                # 使用拖拽开始时的位置作为参考
                if self.drag_start_pos is not None:
                    last_x, last_y = self.drag_start_pos
                else:
                    # 如果没有起始位置，使用舞台中心
                    last_x, last_y = 0, self.stage_height / 2
                
                # 简单的边界限制：保持在预览区域内
                x = max(x_min, min(x_max, last_x))
                y = max(y_min, min(y_max, last_y))
                
                # 如果能够获取到更精确的鼠标位置，进一步优化
                try:
                    # 尝试获取相对于图形的位置
                    inv = self.ax.transData.inverted()
                    x_pixel, y_pixel = event.x, event.y
                    
                    # 获取图形在窗口中的位置
                    bbox = self.ax.bbox
                    if x_pixel < bbox.x0:  # 左边界外
                        x = x_min + 0.5  # 留一点边距
                    elif x_pixel > bbox.x1:  # 右边界外
                        x = x_max - 0.5
                    
                    if y_pixel < bbox.y0:  # 下边界外
                        y = y_min + 0.5
                    elif y_pixel > bbox.y1:  # 上边界外
                        y = y_max - 0.5
                except:
                    # 如果转换失败，使用保守的边界限制
                    pass
                    
            else:
                # 如果无法获取鼠标位置，使用拖拽起始位置
                if self.drag_start_pos is not None:
                    x, y = self.drag_start_pos
                else:
                    # 如果没有起始位置，使用舞台中心
                    x, y = 0, self.stage_height / 2
                # 确保在边界内
                x = max(x_min, min(x_max, x))
                y = max(y_min, min(y_max, y))
            
            self.drag_end_pos = (x, y)
            print(f"元素在预览区域外释放，限制到边缘位置: ({x:.2f}, {y:.2f})")
            
        # 如果位置没有变化，不显示确认对话框
        if self.drag_start_pos == self.drag_end_pos:
            self.dragging = False
            self.drag_item = None
            self.drag_type = None
            self.drag_index = None
            self.drag_start_pos = None
            self.drag_end_pos = None
            self._drag_history_saved = False  # 重置拖动历史保存标志
            return
            
        # 保存最后拖动的项目和位置
        self.last_dragged_item = self.drag_item
        self.last_dragged_pos = self.drag_end_pos
        
        # 记录拖动操作到日志
        if self.drag_item:
            self.log(f"拖动对象: {self.drag_item['name']} → ({self.drag_end_pos[0]:.1f}, {self.drag_end_pos[1]:.1f})", 'info')
        
        # 启用插入关键帧按钮
        self.insert_keyframe_btn.config(state='normal')
        
        # 重置拖动状态
        self.dragging = False
        self.drag_item = None
        self.drag_type = None
        self.drag_index = None
        self.drag_start_pos = None
        self.drag_end_pos = None
        self._drag_history_saved = False  # 重置拖动历史保存标志
    
    def on_mouse_scroll(self, event):
        """处理鼠标滚轮事件 - 缩放舞台预览"""
        # event.button: 'up' 表示向上滚动（放大），'down' 表示向下滚动（缩小）
        if event.button == 'up':
            # 放大：增加缩放比例
            new_zoom = self.zoom_scale * 1.1
        elif event.button == 'down':
            # 缩小：减少缩放比例
            new_zoom = self.zoom_scale / 1.1
        else:
            return  # 其他按钮事件不处理
        
        # 限制缩放范围
        new_zoom = max(self.min_zoom, min(self.max_zoom, new_zoom))
        
        # 如果缩放比例没有变化，直接返回
        if abs(new_zoom - self.zoom_scale) < 0.001:
            return
        
        # 更新缩放比例
        old_zoom = self.zoom_scale
        self.zoom_scale = new_zoom
        
        # 更新舞台预览
        self.update_stage_preview()
        
        # 显示缩放信息
        zoom_percent = int(self.zoom_scale * 100)
        print(f"🔍 缩放: {zoom_percent}% (从 {int(old_zoom*100)}% 到 {zoom_percent}%)")
        
        # 在日志窗口显示缩放比例（可选）
        if zoom_percent % 10 == 0 or zoom_percent in [30, 300]:  # 只在整10%或极值时显示
            self.log(f"🔍 缩放: {zoom_percent}%", 'info')

    def insert_keyframe(self):
        """插入关键帧"""
        if not self.last_dragged_item:
            return
            
        # 清除该元素的临时位置覆盖（用户手动移动后确认位置）
        element_id = self.get_element_id(self.last_dragged_item)
        if element_id in self.temp_position_overrides:
            self.temp_position_overrides.pop(element_id)
            
        # 添加关键帧
        if self.current_frame not in self.last_dragged_item["keyframes"]:
            # 保存历史记录
            self.save_state_to_history(f"插入关键帧 ({self.last_dragged_item['name']} @ {int(self.current_second)}秒)")
            
            # 更新位置
            self.last_dragged_item["positions"][self.current_frame] = self.last_dragged_pos
            self.last_dragged_item["keyframes"].append(self.current_frame)
            
            # 更新中间帧
            self.update_intermediate_frames(self.last_dragged_item)
            
            # 更新显示
            self.update_stage_preview()
            
            # 显示成功提示
            self.log(f"✓ 在第 {int(self.current_second)}秒 插入关键帧", 'success')
            
        # 禁用插入关键帧按钮
        self.insert_keyframe_btn.config(state='disabled')
        
        # 清除最后拖动的状态
        self.last_dragged_item = None
        self.last_dragged_pos = None


    def batch_insert_keyframe(self):
        """为所有演员和道具在当前帧插入关键帧，保持它们的当前位置"""
        # 保存历史记录
        self.save_state_to_history(f"批量插入关键帧 (@ {int(self.current_second)}秒)")
        
        count = 0
        
        # 为所有演员添加关键帧
        for actor in self.actors:
            if self.current_frame not in actor["keyframes"]:
                # 获取演员的当前实际位置（与update_stage_preview中的逻辑一致）
                if actor["keyframes"]:  # 如果有关键帧
                    # 找到当前帧之前和之后的关键帧
                    prev_frame = max([f for f in actor["keyframes"] if f <= self.current_frame], default=None)
                    next_frame = min([f for f in actor["keyframes"] if f > self.current_frame], default=None)
                    
                    if prev_frame is not None:
                        if next_frame is not None:
                            # 在两个关键帧之间进行插值
                            current_pos = actor["positions"][self.current_frame]
                        else:
                            # 使用最后一个关键帧的位置
                            current_pos = actor["positions"][prev_frame]
                    else:
                        # 使用初始位置
                        current_pos = actor["positions"][0]
                else:
                    # 没有关键帧时使用初始位置
                    current_pos = actor["positions"][0]
                
                # 在当前帧插入关键帧，位置为当前实际位置
                actor["positions"][self.current_frame] = current_pos
                actor["keyframes"].append(self.current_frame)
                actor["keyframes"].sort()
                self.update_intermediate_frames(actor)
                count += 1
                print(f"为演员 {actor['name']} 在第 {self.current_frame} 帧插入关键帧，位置: {current_pos}")
        
        # 为所有道具添加关键帧
        for prop in self.props:
            if self.current_frame not in prop["keyframes"]:
                # 获取道具的当前实际位置（与update_stage_preview中的逻辑一致）
                if prop["keyframes"]:  # 如果有关键帧
                    # 找到当前帧之前和之后的关键帧
                    prev_frame = max([f for f in prop["keyframes"] if f <= self.current_frame], default=None)
                    next_frame = min([f for f in prop["keyframes"] if f > self.current_frame], default=None)
                    
                    if prev_frame is not None:
                        if next_frame is not None:
                            # 在两个关键帧之间进行插值
                            current_pos = prop["positions"][self.current_frame]
                        else:
                            # 使用最后一个关键帧的位置
                            current_pos = prop["positions"][prev_frame]
                    else:
                        # 使用初始位置
                        current_pos = prop["positions"][0]
                else:
                    # 没有关键帧时使用初始位置
                    current_pos = prop["positions"][0]
                
                # 在当前帧插入关键帧，位置为当前实际位置
                prop["positions"][self.current_frame] = current_pos
                prop["keyframes"].append(self.current_frame)
                prop["keyframes"].sort()
                self.update_intermediate_frames(prop)
                count += 1
                print(f"为道具 {prop['name']} 在第 {self.current_frame} 帧插入关键帧，位置: {current_pos}")
        
        # 更新显示
        self.update_stage_preview()
        self.on_keyframe_list_select(None)
        
        # 显示操作结果
        current_time = int(self.current_second)
        if count > 0:
            self.log(f"✓ 批量插入完成: 已为 {count} 个元素在第 {current_time}秒 插入关键帧", 'success')
        else:
            self.log(f"所有元素在第 {current_time}秒 都已有关键帧", 'info')

    def delete_actor(self):
        """删除选中的演员"""
        selected = self.keyframe_listbox.curselection()
        if not selected:
            messagebox.showwarning("警告", "请先选择一个演员")
            return
            
        index = selected[0]
        if index >= len(self.actors):
            messagebox.showwarning("警告", "请选择一个演员")
            return
            
        # 确认删除
        if not messagebox.askyesno("确认", f"确定要删除演员 {self.actors[index]['name']} 吗？"):
            return
        
        # 保存历史记录
        self.save_state_to_history(f"删除演员 ({self.actors[index]['name']})")
            
        # 删除演员
        del self.actors[index]
        
        # 更新列表显示
        self.keyframe_listbox.delete(index)
        
        # 清空关键帧表格
        for row in self.keyframe_tree.get_children():
            self.keyframe_tree.delete(row)
        
        # 更新舞台预览
        self.update_stage_preview()
        
        # 显示成功提示
        self.log("✓ 演员已删除", 'success')
        
    def delete_prop(self):
        """删除选中的道具"""
        selected = self.keyframe_listbox.curselection()
        if not selected:
            messagebox.showwarning("警告", "请先选择一个道具")
            return
            
        index = selected[0]
        if index < len(self.actors):
            messagebox.showwarning("警告", "请选择一个道具")
            return
            
        prop_index = index - len(self.actors)
        if prop_index >= len(self.props):
            messagebox.showwarning("警告", "请选择一个道具")
            return
            
        # 确认删除
        if not messagebox.askyesno("确认", f"确定要删除道具 {self.props[prop_index]['name']} 吗？"):
            return
        
        # 保存历史记录
        self.save_state_to_history(f"删除道具 ({self.props[prop_index]['name']})")
            
        # 删除道具
        del self.props[prop_index]
        
        # 更新列表显示
        self.keyframe_listbox.delete(index)
        
        # 清空关键帧表格
        for row in self.keyframe_tree.get_children():
            self.keyframe_tree.delete(row)
            
        # 更新舞台预览
        self.update_stage_preview()
        
        # 显示成功提示
        self.log("✓ 道具已删除", 'success')

    def update_text_box(self):
        """更新文本框内容"""
        try:
            # 确保durations字段存在
            if "durations" not in self.text_box:
                self.text_box["durations"] = {}
            
            # 获取秒数
            seconds = float(self.text_second_entry.get())
            if seconds < 0 or seconds > self.total_seconds:  # 修改为 > 而不是 >=
                raise ValueError(f"时间必须在0到{self.total_seconds}秒之间")
            
            # 获取持续时间
            duration = float(self.text_duration_entry.get())
            if duration <= 0:
                raise ValueError("持续时间必须大于0")
            
            # 更新字体大小
            font_size = float(self.text_size_entry.get())
            if font_size <= 0:
                raise ValueError("字体大小必须大于0")
            self.text_box["font_size"] = font_size
            
            # 获取文本内容
            content = self.text_content_entry.get()
            
            # 计算开始和结束帧
            start_frame = int(seconds * self.fps)
            end_frame = int((seconds + duration) * self.fps)
            if end_frame > self.total_frames:
                end_frame = self.total_frames
            
            # 清除这个时间段内之前的文本内容
            for frame in range(start_frame, end_frame):
                self.text_box["contents"][frame] = ""
            
            # 移除这个时间段内之前的持续时间记录
            frames_to_remove = []
            for start_f, duration_f in self.text_box["durations"].items():
                if start_f >= start_frame and start_f < end_frame:
                    frames_to_remove.append(start_f)
                elif start_f < start_frame and start_f + duration_f > start_frame:
                    frames_to_remove.append(start_f)
            for frame in frames_to_remove:
                self.text_box["durations"].pop(frame, None)
            
            # 应用新的文本内容到持续时间范围内
            if content.strip():  # 只有当文本不为空时才添加
                duration_frames = end_frame - start_frame
                self.text_box["durations"][start_frame] = duration_frames
                for frame in range(start_frame, end_frame):
                    self.text_box["contents"][frame] = content
            
            # 如果修改的是当前时间，更新显示
            if abs(seconds - self.current_second) < 0.001:  # 使用小误差比较浮点数
                self.update_stage_preview()
            else:
                # 切换到指定时间
                self.current_second = seconds
                self.current_frame = start_frame
                self.time_scale.set(seconds)
                self.update_stage_preview()
            
            print(f"文本设置完成: \"{content}\" 从{seconds}秒开始，持续{duration}秒")
            
        except ValueError as e:
            messagebox.showerror("错误", str(e))
    
    def get_text_duration_at_frame(self, frame):
        """获取指定帧的文本持续时间"""
        # 确保durations字段存在
        if "durations" not in self.text_box:
            self.text_box["durations"] = {}
        
        for start_frame, duration_frames in self.text_box["durations"].items():
            if start_frame <= frame < start_frame + duration_frames:
                return duration_frames / self.fps  # 转换为秒
        return 1.0  # 默认1秒

    def switch_frame(self):
        """切换到指定时间"""
        try:
            seconds = float(self.frame_switch_entry.get())
            if seconds < 0 or seconds > self.total_seconds:  # 修改为 > 而不是 >=
                raise ValueError(f"时间必须在0到{self.total_seconds}秒之间")
            
            # 转换为帧数
            frame = int(seconds * self.fps)
            
            # 更新当前帧和时间
            self.current_frame = frame
            self.current_second = seconds
            self.time_scale.set(seconds)
            
            # 更新文本框内容显示
            self.text_content_entry.delete(0, tk.END)
            if (self.current_frame < len(self.text_box["contents"]) and 
                self.current_frame >= 0 and 
                len(self.text_box["contents"]) > 0):
                self.text_content_entry.insert(0, self.text_box["contents"][self.current_frame])
            else:
                self.text_content_entry.insert(0, "")
            
            # 更新时间显示
            self.text_second_entry.delete(0, tk.END)
            self.text_second_entry.insert(0, str(self.current_second))
            
            # 更新舞台预览
            self.update_stage_preview()
            
        except ValueError as e:
            messagebox.showerror("错误", str(e))

    def on_speed_change(self, event):
        """处理播放速度变化事件"""
        try:
            # 从选择的值中提取速度数值（去掉'x'后缀）
            speed_str = self.speed_var.get().rstrip('x')
            new_speed = float(speed_str)
            if new_speed <= 0:
                raise ValueError("播放速度必须大于0")
            
            self.playback_speed = new_speed
            
            # 如果正在播放，重置时间记录
            if self.animation_loop.running:
                self.last_frame_time = self.root.tk.call('clock', 'milliseconds')
                self.fps_start_time = self.last_frame_time
                self.frame_count = 0
            
        except ValueError as e:
            messagebox.showerror("错误", str(e))
            # 恢复原来的值
            self.speed_var.set(f"{self.playback_speed:.2f}x")

    def export_animation(self):
        """导出动画为GIF文件"""
        # 检查动画是否正在播放
        if hasattr(self, 'animation_loop') and self.animation_loop.running:
            messagebox.showwarning("警告", "请先停止动画播放再进行导出")
            return
        
        # 初始化进度窗口变量（在try块之前）
        progress_window = None
            
        try:
            # 获取导出帧率
            export_fps = int(self.export_fps_entry.get())
            if export_fps <= 0:
                raise ValueError("导出帧率必须大于0")
            
            # 创建导出目录
            export_dir = "exports"
            if not os.path.exists(export_dir):
                os.makedirs(export_dir)
            
            # 让用户选择保存位置
            export_path = filedialog.asksaveasfilename(
                defaultextension=".gif",
                initialdir=export_dir,
                initialfile="stage_animation.gif",
                filetypes=[("GIF files", "*.gif"), ("All files", "*.*")]
            )
            
            if not export_path:  # 用户取消选择
                return
            
            # 创建进度条窗口
            progress_window = tk.Toplevel(self.root)
            progress_window.title("GIF导出进度")
            progress_window.geometry("400x180")
            progress_window.resizable(False, False)
            
            # 设置窗口在主窗口前面
            progress_window.transient(self.root)
            progress_window.grab_set()
            
            # 添加进度标签
            progress_label = ttk.Label(progress_window, text="正在准备GIF导出...", font=('Arial', 10))
            progress_label.pack(pady=15)
            
            # 添加进度条
            progress_bar = ttk.Progressbar(progress_window, length=350, mode='determinate')
            progress_bar.pack(pady=10)
            
            # 添加状态标签
            status_label = ttk.Label(progress_window, text="初始化中...", font=('Arial', 9))
            status_label.pack(pady=5)
            
            # 添加帧计数标签
            frame_label = ttk.Label(progress_window, text="", font=('Arial', 8))
            frame_label.pack(pady=5)
            
            # 添加取消按钮
            cancel_button = ttk.Button(progress_window, text="取消", 
                                     command=lambda: setattr(self, '_cancel_export', True))
            cancel_button.pack(pady=10)
            
            # 初始化取消标志
            self._cancel_export = False
            
            # 更新窗口
            progress_window.update()
            
            # 计算需要导出的总帧数
            total_export_frames = int(self.total_seconds * export_fps)
            
            # 确保有帧数可以导出
            if total_export_frames <= 0:
                progress_window.destroy()
                raise ValueError("没有可导出的帧数")
            
            # 更新进度信息
            progress_label.config(text=f"准备导出 {total_export_frames} 帧GIF动画")
            frame_label.config(text=f"帧率: {export_fps} FPS | 时长: {self.total_seconds:.1f}秒")
            progress_window.update()
            
            # 创建新的图形用于导出
            export_fig = Figure(figsize=(10, 8))  # 使用能被2整除的尺寸
            export_ax = export_fig.add_subplot(111)
            
            # 设置导出图形的样式
            invisible_width = self.stage_width / 8  # 左右备台区域宽度
            export_ax.set_xlim(-self.stage_width/2 - invisible_width, self.stage_width/2 + invisible_width)
            # 计算后方备台区域高度以调整导出视图范围
            backstage_height = self.stage_height / 8
            export_ax.set_ylim(0, self.stage_height + backstage_height + 1)  # 包含后方备台区域
            export_ax.set_aspect('equal')
            export_ax.grid(True)
            
            # 显示进度信息
            print(f"开始导出GIF动画，总帧数: {total_export_frames}")
            
            # 定义更新进度的函数
            def update_progress(current, total, status=""):
                if hasattr(self, '_cancel_export') and self._cancel_export:
                    return False  # 返回False表示取消
                
                progress = (current / total) * 100
                progress_bar['value'] = progress
                status_label.config(text=status)
                frame_label.config(text=f"正在生成: {current}/{total} 帧 ({progress:.1f}%)")
                progress_window.update()
                return True  # 继续
            
            # 定义检查位置是否在可见区域内的函数（包括舞台和备台区域）
            def is_position_in_stage(pos):
                x, y = pos
                invisible_width = self.stage_width / 8  # 左右备台区域宽度
                backstage_height = self.stage_height / 8  # 后方备台区域高度
                
                # 检查X轴范围：包括左右备台区域
                x_in_range = (-self.stage_width/2 - invisible_width <= x <= self.stage_width/2 + invisible_width)
                
                # 检查Y轴范围：包括舞台和后方备台区域
                y_in_range = (0 <= y <= self.stage_height + backstage_height)
                
                return x_in_range and y_in_range
            
            # 创建动画
            frame_count = [0]  # 使用列表来在闭包中修改值
            
            def update(frame):
                frame_count[0] = frame + 1
                
                # 更新进度
                if not update_progress(frame_count[0], total_export_frames, "正在生成动画帧..."):
                    return []  # 如果取消，返回空列表
                
                export_ax.clear()
                
                # 设置显示范围
                invisible_width = self.stage_width / 8  # 左右备台区域宽度
                export_ax.set_xlim(-self.stage_width/2 - invisible_width, self.stage_width/2 + invisible_width)
                # 计算后方备台区域高度以调整导出视图范围
                backstage_height = self.stage_height / 8
                export_ax.set_ylim(0, self.stage_height + backstage_height + 1)  # 包含后方备台区域
                export_ax.set_aspect('equal')
                export_ax.grid(True)
                
                # 计算当前时间点
                current_time = frame / export_fps
                current_frame = int(current_time * self.fps)
                
                # 确保current_frame不超出范围
                current_frame = min(current_frame, self.total_frames - 1)
                
                # 绘制舞台边界
                stage_rect = Rectangle((-self.stage_width/2, 0), self.stage_width, self.stage_height, 
                                     fill=False, color='black', linewidth=2)
                export_ax.add_patch(stage_rect)
                
                # 绘制舞台中线
                export_ax.axvline(x=0, ymin=0, ymax=self.stage_height/(self.stage_height + backstage_height + 1), 
                                color='red', linestyle='--', linewidth=0.8, alpha=0.5)
                
                # 绘制备台区域
                invisible_width = self.stage_width / 8  # 左右备台区域宽度为舞台宽度的1/8
                
                # 左侧备台区域
                left_invisible = Rectangle((-self.stage_width/2 - invisible_width, 0), 
                                         invisible_width, self.stage_height,
                                         fill=True, color='gray', alpha=0.3)
                export_ax.add_patch(left_invisible)
                export_ax.text(-self.stage_width/2 - invisible_width/2, self.stage_height/2, '左侧\n备台区域', 
                             rotation=90, ha='center', va='center', color='gray', alpha=0.7, fontsize=12)
                
                # 右侧备台区域
                right_invisible = Rectangle((self.stage_width/2, 0), 
                                          invisible_width, self.stage_height,
                                          fill=True, color='gray', alpha=0.3)
                export_ax.add_patch(right_invisible)
                export_ax.text(self.stage_width/2 + invisible_width/2, self.stage_height/2, '右侧\n备台区域', 
                             rotation=90, ha='center', va='center', color='gray', alpha=0.7, fontsize=12)
                
                # 后方备台区域 - 连接左右两侧
                backstage_height = self.stage_height / 8  # 后方备台区域高度为舞台高度的1/8
                upper_backstage = Rectangle((-self.stage_width/2 - invisible_width, self.stage_height), 
                                           self.stage_width + 2 * invisible_width, backstage_height,
                                           fill=True, color='gray', alpha=0.3)
                export_ax.add_patch(upper_backstage)
                export_ax.text(0, self.stage_height + backstage_height/2, '后方备台区域', 
                             ha='center', va='center', color='gray', alpha=0.7, fontsize=12)
                
                # 添加观众区域标识
                export_ax.text(0, -1.5, '观众区域', ha='center', va='center', 
                             color='gray', alpha=0.7, fontsize=12,
                             bbox=dict(facecolor='white', alpha=0.3, edgecolor='none', pad=3))
                
                # 绘制所有演员
                for actor in self.actors:
                    # 获取当前位置
                    if actor["keyframes"]:  # 如果有关键帧
                        # 找到当前帧之前和之后的关键帧
                        prev_frame = max([f for f in actor["keyframes"] if f <= current_frame], default=None)
                        next_frame = min([f for f in actor["keyframes"] if f > current_frame], default=None)
                        
                        if prev_frame is not None:
                            if next_frame is not None:
                                # 在两个关键帧之间进行插值
                                pos = actor["positions"][current_frame]
                            else:
                                # 使用最后一个关键帧的位置
                                pos = actor["positions"][prev_frame]
                        else:
                            # 使用初始位置
                            pos = actor["positions"][0]
                    else:
                        pos = actor["positions"][0]
                        
                    # 检查位置是否在舞台区域内
                    if is_position_in_stage(pos):
                        # 获取颜色，如果没有颜色属性则使用默认颜色
                        color = actor.get("color", "blue")
                        # 获取字号，如果没有字号属性则使用默认字号
                        font_size = actor.get("font_size", 10)
                        
                        if actor["shape"] == "circle":
                            circle = Circle((pos[0], pos[1]), actor["size"], 
                                         fill=False,  # 不填充
                                         color=color, 
                                         linewidth=2)
                            export_ax.add_patch(circle)
                            export_ax.text(pos[0], pos[1], actor["name"], "siz                                      ha='center', va='center', 
                                         color=color,  # 文字颜色与轮廓一致
                                         fontsize=font_size,  # 使用自定义字号
                                         weight='bold')
                        elif actor["shape"] == "square":
                            rect = Rectangle((pos[0]-actor["size"]/2, pos[1]-actor["size"]/2),
                                           actor["size"], actor["size"], 
                                           fill=False,  # 不填充
                                           color=color, 
                                           linewidth=2)
                            export_ax.add_patch(rect)
                            export_ax.text(pos[0], pos[1], actor["name"], 
                                         ha='center', va='center', 
                                         color=color,  # 文字颜色与轮廓一致
                                         fontsize=font_size,  # 使用自定义字号
                                         weight='bold')
                        elif actor["shape"] == "triangle":
                            triangle = Polygon([(pos[0], pos[1]+actor["size"]),
                                              (pos[0]-actor["size"], pos[1]-actor["size"]),
                                              (pos[0]+actor["size"], pos[1]-actor["size"])], 
                                             fill=False,  # 不填充
                                             color=color, 
                                             linewidth=2)
                            export_ax.add_patch(triangle)
                            export_ax.text(pos[0], pos[1], actor["name"], 
                                         ha='center', va='center', 
                                         color=color,  # 文字颜色与轮廓一致
                                         fontsize=font_size,  # 使用自定义字号
                                         weight='bold')
                
                # 绘制所有道具
                for prop in self.props:
                    # 获取当前位置
                    if prop["keyframes"]:  # 如果有关键帧
                        # 找到当前帧之前和之后的关键帧
                        prev_frame = max([f for f in prop["keyframes"] if f <= current_frame], default=None)
                        next_frame = min([f for f in prop["keyframes"] if f > current_frame], default=None)
                        
                        if prev_frame is not None:
                            if next_frame is not None:
                                # 在两个关键帧之间进行插值
                                pos = prop["positions"][current_frame]
                            else:
                                # 使用最后一个关键帧的位置
                                pos = prop["positions"][prev_frame]
                        else:
                            # 使用初始位置
                            pos = prop["positions"][0]
                    else:
                        pos = prop["positions"][0]
                        
                    # 检查位置是否在舞台区域内
                    if is_position_in_stage(pos):
                        # 获取颜色，如果没有颜色属性则使用默认颜色
                        color = prop.get("color", "red")
                        # 获取字号，如果没有字号属性则使用默认字号
                        font_size = prop.get("font_size", 10)
                        
                        if prop["shape"] == "rectangle":
                            rect = Rectangle((pos[0]-prop["width"]/2, pos[1]-prop["height"]/2),
                                           prop["width"], prop["height"], 
                                           fill=False,  # 不填充
                                           color=color, 
                                           linewidth=2)
                            export_ax.add_patch(rect)
                            export_ax.text(pos[0], pos[1], prop["name"], 
                                         ha='center', va='center', 
                                         color=color,  # 文字颜色与轮廓一致
                                         fontsize=font_size,  # 使用自定义字号
                                         weight='bold')
                        elif prop["shape"] == "circle":
                            circle = Circle((pos[0], pos[1]), prop["width"]/2, 
                                         fill=False,  # 不填充
                                         color=color, 
                                         linewidth=2)
                            export_ax.add_patch(circle)
                            export_ax.text(pos[0], pos[1], prop["name"], 
                                         ha='center', va='center', 
                                         color=color,  # 文字颜色与轮廓一致
                                         fontsize=font_size,  # 使用自定义字号
                                         weight='bold')
                        elif prop["shape"] == "triangle":
                            triangle = Polygon([(pos[0], pos[1]+prop["height"]/2),
                                              (pos[0]-prop["width"]/2, pos[1]-prop["height"]/2),
                                              (pos[0]+prop["width"]/2, pos[1]-prop["height"]/2)], 
                                             fill=False,  # 不填充
                                             color=color, 
                                             linewidth=2)
                            export_ax.add_patch(triangle)
                            export_ax.text(pos[0], pos[1], prop["name"], 
                                         ha='center', va='center', 
                                         color=color,  # 文字颜色与轮廓一致
                                         fontsize=font_size,  # 使用自定义字号
                                         weight='bold')
                
                # 绘制文本框 - 放置在后方备台区域上方且不重合
                if current_frame < len(self.text_box["contents"]) and self.text_box["contents"][current_frame]:
                    backstage_height = self.stage_height / 8  # 后方备台区域高度
                    text_y_position = self.stage_height + backstage_height + 0.5  # 在后方备台区域上方0.5单位
                    export_ax.text(0, text_y_position,
                                self.text_box["contents"][current_frame],
                                ha='center', va='center',
                                fontsize=self.text_box["font_size"],
                                color='black',
                                bbox=dict(facecolor='white', alpha=0.7, edgecolor='black', pad=5))
                
                # 设置标题
                export_ax.set_title(f'时间: {current_time:.1f}秒', fontsize=12)
                
                # 隐藏坐标轴
                export_ax.set_axis_off()
                
                # 返回空列表以满足FuncAnimation的要求
                return []
            
            # 创建动画 - 禁用blit以确保稳定性
            anim = animation.FuncAnimation(export_fig, update, frames=total_export_frames,
                                         interval=1000/export_fps, blit=False)
            
            # 更新状态
            status_label.config(text="正在保存GIF文件...")
            progress_window.update()
            
            # 导出动画为GIF
            anim.save(export_path, writer='pillow', fps=export_fps)
            
            # 清理资源
            plt.close(export_fig)
            
            # 更新最终状态
            if progress_window is not None:
                progress_bar['value'] = 100
                status_label.config(text="导出完成！")
                frame_label.config(text=f"成功导出 {total_export_frames} 帧")
                cancel_button.config(text="关闭")
                progress_window.update()
                
                print(f"GIF导出完成: {export_path}")
                
                # 等待用户点击关闭或自动关闭
                progress_window.after(2000, progress_window.destroy)  # 2秒后自动关闭
                
                # 显示成功消息
                self.log(f"✓ GIF动画导出成功: {os.path.basename(export_path)}", 'success')
            
        except ValueError as e:
            if progress_window is not None:
                progress_window.destroy()
            messagebox.showerror("错误", str(e))
        except Exception as e:
            if progress_window is not None:
                progress_window.destroy()
            messagebox.showerror("错误", f"导出失败: {str(e)}")
            print(f"导出错误详情: {str(e)}")  # 添加详细错误信息打印
        finally:
            # 清理取消标志
            if hasattr(self, '_cancel_export'):
                delattr(self, '_cancel_export')

    def save_project(self):
        """保存当前项目"""
        try:
            # 让用户选择保存位置
            file_path = filedialog.asksaveasfilename(
                defaultextension=".json",
                filetypes=[("JSON files", "*.json"), ("All files", "*.*")],
                title="保存项目"
            )
            
            if not file_path:  # 用户取消选择
                return
            
            # 准备保存的数据
            project_data = {
                "stage_width": self.stage_width,
                "stage_height": self.stage_height,
                "total_frames": self.total_frames,
                "actors": self.actors,
                "props": self.props,
                "text_box": self.text_box
            }
            
            # 保存到文件
            with open(file_path, 'w', encoding='utf-8') as f:
                json.dump(project_data, f, ensure_ascii=False, indent=2)
            
            # 显示成功消息
            self.log(f"✓ 项目已保存: {os.path.basename(file_path)}", 'success')
            
        except Exception as e:
            messagebox.showerror("错误", f"保存失败: {str(e)}")

    def load_project(self):
        """导入项目"""
        try:
            # 让用户选择文件
            file_path = filedialog.askopenfilename(
                filetypes=[("JSON files", "*.json"), ("All files", "*.*")],
                title="导入项目"
            )
            
            if not file_path:  # 用户取消选择
                return
            
            # 停止任何正在进行的动画
            if hasattr(self, 'animation_loop') and self.animation_loop.running:
                self.animation_loop.stop()
            
            # 读取文件
            with open(file_path, 'r', encoding='utf-8') as f:
                project_data = json.load(f)
            
            # 兼容性检查和数据修复
            print(f"正在导入项目文件: {file_path}")
            print(f"项目数据键: {list(project_data.keys())}")
            
            # 更新舞台尺寸
            self.stage_width = project_data.get("stage_width", 20)  # 默认值
            self.stage_height = project_data.get("stage_height", 15)  # 默认值
            self.width_entry.delete(0, tk.END)
            self.width_entry.insert(0, str(self.stage_width))
            self.height_entry.delete(0, tk.END)
            self.height_entry.insert(0, str(self.stage_height))
            
            # 更新总帧数
            self.total_frames = project_data.get("total_frames", 600)  # 默认值
            self.total_seconds = self.total_frames / self.fps
            
            # 更新演员和道具，确保兼容性
            self.actors = project_data.get("actors", [])
            self.props = project_data.get("props", [])
            
            # 为演员和道具添加缺失的字段
            for actor in self.actors:
                # 确保所有必需字段存在
                if "color" not in actor:
                    actor["color"] = "blue"
                if "font_size" not in actor:
                    actor["font_size"] = 10
                if "keyframes" not in actor:
                    actor["keyframes"] = [0]
                else:
                    # 确保关键帧是整数（修复字符串关键帧问题）
                    actor["keyframes"] = [int(f) for f in actor["keyframes"]]
                if "positions" not in actor or len(actor["positions"]) != self.total_frames:
                    # 重建位置数组
                    default_pos = (0, 5)
                    actor["positions"] = [default_pos for _ in range(self.total_frames)]
                    
            for prop in self.props:
                # 确保所有必需字段存在
                if "color" not in prop:
                    prop["color"] = "red"
                if "font_size" not in prop:
                    prop["font_size"] = 10
                if "keyframes" not in prop:
                    prop["keyframes"] = [0]
                else:
                    # 确保关键帧是整数（修复字符串关键帧问题）
                    prop["keyframes"] = [int(f) for f in prop["keyframes"]]
                if "positions" not in prop or len(prop["positions"]) != self.total_frames:
                    # 重建位置数组
                    default_pos = (0, 8)
                    prop["positions"] = [default_pos for _ in range(self.total_frames)]
            
            # 更新文本框
            self.text_box = project_data.get("text_box", {
                "contents": ["" for _ in range(self.total_frames)],
                "font_size": 12,
                "position": (0, self.stage_height + 1.5),
                "durations": {}
            })
            
            # 确保文本框字段完整
            if "contents" not in self.text_box:
                self.text_box["contents"] = ["" for _ in range(self.total_frames)]
            elif len(self.text_box["contents"]) != self.total_frames:
                # 调整文本内容数组长度
                old_contents = self.text_box["contents"]
                self.text_box["contents"] = ["" for _ in range(self.total_frames)]
                for i in range(min(len(old_contents), self.total_frames)):
                    self.text_box["contents"][i] = old_contents[i]
                    
            if "font_size" not in self.text_box:
                self.text_box["font_size"] = 12
            if "position" not in self.text_box:
                self.text_box["position"] = (0, self.stage_height + 1.5)
            if "durations" not in self.text_box:
                self.text_box["durations"] = {}
            else:
                # 确保durations字典的键是整数（修复字符串键问题）
                old_durations = self.text_box["durations"]
                self.text_box["durations"] = {}
                for start_frame, duration_frames in old_durations.items():
                    # 将字符串键转换为整数键
                    int_start_frame = int(start_frame)
                    int_duration_frames = int(duration_frames) if isinstance(duration_frames, str) else duration_frames
                    self.text_box["durations"][int_start_frame] = int_duration_frames
            
            # 清空并更新关键帧列表
            self.keyframe_listbox.delete(0, tk.END)
            for actor in self.actors:
                self.keyframe_listbox.insert(tk.END, f"演员: {actor['name']}")
            for prop in self.props:
                self.keyframe_listbox.insert(tk.END, f"道具: {prop['name']}")
            
            # 更新时间轴
            self.time_scale.config(to=self.total_seconds)
            
            # 重置所有状态变量
            self.current_frame = 0
            self.current_second = 0
            self.is_playing = False
            self.fixed_view_range = None
            
            # 清理临时状态
            self.temp_position_overrides.clear()
            self.temp_keyframes.clear()
            
            # 重置拖动状态
            self.dragging = False
            self.drag_item = None
            self.drag_type = None
            self.drag_index = None
            self.drag_start_pos = None
            self.drag_end_pos = None
            
            # 重置时间轴滑块标志
            self.is_time_scale_updating = False
            
            # 更新时间轴滑块位置
            self.time_scale.set(0)
            
            # 更新文本框显示
            self.text_content_entry.delete(0, tk.END)
            if self.text_box["contents"]:
                self.text_content_entry.insert(0, self.text_box["contents"][0])
            self.text_second_entry.delete(0, tk.END)
            self.text_second_entry.insert(0, "0")
            
            # 更新持续时间显示
            self.text_duration_entry.delete(0, tk.END)
            current_duration = self.get_text_duration_at_frame(0)
            self.text_duration_entry.insert(0, str(current_duration))
            
            # 更新总秒数显示
            self.seconds_entry.delete(0, tk.END)
            self.seconds_entry.insert(0, str(self.total_seconds))
            
            # 更新显示
            self.update_stage_preview()
            
            # 强制更新画布
            self.canvas.draw()
            
            print(f"项目导入成功: 演员{len(self.actors)}个, 道具{len(self.props)}个, 总时长{self.total_seconds}秒")
            
            # 显示成功消息
            self.log(f"✓ 项目已导入: 演员{len(self.actors)}个, 道具{len(self.props)}个, 总时长{self.total_seconds}秒", 'success')
            
        except Exception as e:
            error_msg = f"导入失败: {str(e)}"
            print(f"导入错误详情: {error_msg}")
            import traceback
            traceback.print_exc()
            messagebox.showerror("错误", error_msg)

    def update_stage_size(self):
        """更新舞台尺寸"""
        try:
            new_width = float(self.width_entry.get())
            new_height = float(self.height_entry.get())
            
            if new_width <= 0 or new_height <= 0:
                raise ValueError("舞台尺寸必须大于0")
                
            self.stage_width = new_width
            self.stage_height = new_height
            
            # 更新舞台预览
            self.update_stage_preview()
            
        except ValueError as e:
            messagebox.showerror("错误", str(e))
            # 恢复原来的值
            self.width_entry.delete(0, tk.END)
            self.width_entry.insert(0, str(self.stage_width))
            self.height_entry.delete(0, tk.END)
            self.height_entry.insert(0, str(self.stage_height))

    def update_timeline_settings(self):
        """更新时间轴设置"""
        try:
            # 更新总秒数
            new_seconds = float(self.seconds_entry.get())
            if new_seconds <= 0:
                raise ValueError("总秒数必须大于0")
            new_frames = int(new_seconds * self.fps)
            old_frames = self.total_frames
            self.total_seconds = new_seconds
            self.total_frames = new_frames

            # 更新所有演员的位置数组
            for actor in self.actors:
                old_positions = actor["positions"]
                actor["positions"] = [(0, 0) for _ in range(new_frames)]
                for i in range(min(old_frames, new_frames)):
                    actor["positions"][i] = old_positions[i]
                actor["keyframes"] = [frame for frame in actor["keyframes"] if frame < new_frames]
                # 更新中间帧插值
                if len(actor["keyframes"]) >= 2:
                    self.update_intermediate_frames(actor)

            # 更新所有道具的位置数组
            for prop in self.props:
                old_positions = prop["positions"]
                prop["positions"] = [(0, 0) for _ in range(new_frames)]
                for i in range(min(old_frames, new_frames)):
                    prop["positions"][i] = old_positions[i]
                prop["keyframes"] = [frame for frame in prop["keyframes"] if frame < new_frames]
                # 更新中间帧插值
                if len(prop["keyframes"]) >= 2:
                    self.update_intermediate_frames(prop)

            # 更新文本框内容数组
            old_contents = self.text_box["contents"]
            self.text_box["contents"] = ["" for _ in range(new_frames)]
            for i in range(min(old_frames, new_frames)):
                self.text_box["contents"][i] = old_contents[i]

            # 更新时间轴滑块
            self.time_scale.config(to=new_seconds)
            
            # 如果当前时间超出新的总秒数，重置到开始
            if self.current_second >= new_seconds:
                self.current_second = 0
                self.current_frame = 0
                self.time_scale.set(0)
                
            self.update_stage_preview()
            
        except ValueError as e:
            messagebox.showerror("错误", str(e))
            self.seconds_entry.delete(0, tk.END)
            self.seconds_entry.insert(0, str(self.total_seconds))

    def play_animation(self):
        """开始播放动画"""
        print("开始播放动画")
        try:
            # 设置播放状态并保存当前视图范围
            self.is_playing = True
            self.capture_current_view_range()
            
            # 清除临时位置覆盖（开始播放时）
            self.temp_position_overrides.clear()
            
            # 确保所有中间帧都已更新
            for actor in self.actors:
                if actor["keyframes"]:
                    self.update_intermediate_frames(actor)
            for prop in self.props:
                if prop["keyframes"]:
                    self.update_intermediate_frames(prop)
                    
            # 处理音频播放
            if self.audio_file:
                if not pygame.mixer.music.get_busy():
                    # 如果音频未在播放，从当前时间点开始播放
                    pygame.mixer.music.play(loops=0, start=self.current_second)
                else:
                    # 如果音频已暂停，继续播放
                    pygame.mixer.music.unpause()
                    
            # 启动动画循环
            self.animation_loop.start()
            print("动画循环已启动，视图范围已固定")
            
            # 记录日志
            self.log(f"▶ 开始播放 (从 {self.current_second:.1f}秒)", 'info')
        except Exception as e:
            print(f"播放动画时出错: {str(e)}")
            traceback.print_exc()

    def pause_animation(self):
        """暂停动画"""
        print("暂停动画")
        try:
            # 停止播放状态，恢复动态视图
            self.is_playing = False
            self.fixed_view_range = None
            
            self.animation_loop.stop()
            # 暂停音频播放
            if self.audio_file and pygame.mixer.music.get_busy():
                pygame.mixer.music.pause()
            print("动画已暂停，视图范围已恢复")
            
            # 记录日志
            self.log(f"⏸ 暂停播放 (在 {self.current_second:.1f}秒)", 'info')
        except Exception as e:
            print(f"暂停动画时出错: {str(e)}")
            traceback.print_exc()

    def stop_animation(self):
        """停止动画"""
        print("停止动画")
        try:
            # 停止播放状态，恢复动态视图
            self.is_playing = False
            self.fixed_view_range = None
            
            self.animation_loop.stop()
            # 停止音频播放
            if self.audio_file:
                pygame.mixer.music.stop()
            self.current_second = 0
            self.current_frame = 0
            self.time_scale.set(0)
            self.update_stage_preview()
            print("动画已停止")
            
            # 记录日志
            self.log("⏹ 停止播放 (已重置到起点)", 'info')
        except Exception as e:
            print(f"停止动画时出错: {str(e)}")
            traceback.print_exc()

    def on_play_click(self, event):
        """处理播放按钮点击事件"""
        print("播放按钮被点击")  # 调试信息
        self.play_animation()

    def on_pause_click(self, event):
        """处理暂停按钮点击事件"""
        print("暂停按钮被点击")  # 调试信息
        self.pause_animation()

    def on_stop_click(self, event):
        """处理停止按钮点击事件"""
        print("停止按钮被点击")  # 调试信息
        self.stop_animation()
    
    def toggle_play_pause(self, event):
        """处理空格键：切换播放和暂停状态"""
        # 检查焦点是否在输入框上，如果是则允许正常输入空格
        focused_widget = self.root.focus_get()
        if focused_widget and isinstance(focused_widget, (tk.Entry, ttk.Entry)):
            # 如果焦点在输入框上，不拦截空格键，让输入框正常处理
            return
        
        # 检查是否正在播放
        if self.is_playing:
            print("空格键被按下 - 暂停动画")
            self.pause_animation()
        else:
            print("空格键被按下 - 播放动画")
            self.play_animation()
        # 返回"break"以阻止事件继续传播（防止触发按钮点击）
        return "break"

    def on_time_scale_press(self, event):
        """处理时间轴滑块按下事件"""
        # 标记用户正在拖动时间轴
        self.is_user_dragging_timeline = True
        print("用户开始拖动时间轴")
    
    def on_time_scale_change(self, value):
        """处理时间轴滑块变化事件"""
        # 如果正在更新滑块值，则跳过
        if self.is_time_scale_updating:
            return
            
        try:
            self.is_time_scale_updating = True
            
            # 获取秒数 - 播放过程中不应用吸附，只有用户手动操作时才吸附
            seconds = float(value)
            
            # 确保秒数不超过总秒数
            seconds = min(seconds, self.total_seconds)
            frame = int(seconds * self.fps)
            # 确保帧数不超过总帧数，并确保不小于0
            frame = max(0, min(frame, self.total_frames - 1))
            # 额外检查：确保帧数在文本框内容数组范围内
            if len(self.text_box["contents"]) > 0:
                frame = min(frame, len(self.text_box["contents"]) - 1)
            
            self.current_frame = frame
            self.current_second = seconds
            
            # 清理不再需要的临时关键帧
            self.cleanup_temp_keyframes_on_time_change()
            
            # 清除临时位置覆盖（当时间点改变时）
            self.temp_position_overrides.clear()
            
            # 更新文本框内容显示
            self.text_content_entry.delete(0, tk.END)
            if (self.current_frame < len(self.text_box["contents"]) and 
                self.current_frame >= 0 and 
                len(self.text_box["contents"]) > 0):
                self.text_content_entry.insert(0, self.text_box["contents"][self.current_frame])
            
            # 更新持续时间显示
            self.text_duration_entry.delete(0, tk.END)
            current_duration = self.get_text_duration_at_frame(self.current_frame)
            self.text_duration_entry.insert(0, str(current_duration))
            
            # 更新时间显示 - 只显示整数秒
            self.text_second_entry.delete(0, tk.END)
            self.text_second_entry.insert(0, str(int(self.current_second)))
            
            # 重置拖动状态
            self.dragging = False
            self.drag_item = None
            self.drag_type = None
            self.drag_index = None
            self.drag_start_pos = None
            self.drag_end_pos = None
            
            # 如果正在播放且有音频文件，实时同步音频位置
            if self.audio_file and hasattr(self, 'animation_loop') and self.animation_loop.running:
                # 在拖动时重新同步音频，使用平滑方式减少杂音
                current_volume = pygame.mixer.music.get_volume()
                pygame.mixer.music.set_volume(0.0)
                pygame.mixer.music.stop()
                pygame.mixer.music.set_volume(current_volume)
                pygame.mixer.music.play(loops=0, start=self.current_second)
                # 更新音频开始时间
                self.animation_loop.audio_start_time = self.root.tk.call('clock', 'milliseconds')
                if hasattr(self.animation_loop, 'last_sync_check'):
                    self.animation_loop.last_sync_check = self.animation_loop.audio_start_time
                print(f"拖动时间轴时同步音频到 {self.current_second:.2f} 秒")
            
            # 更新舞台预览
            self.update_stage_preview()
            
        finally:
            self.is_time_scale_updating = False

    def on_time_scale_release(self, event):
        """处理时间轴滑块释放事件"""
        # 取消用户拖动标记
        self.is_user_dragging_timeline = False
        print("用户释放时间轴")
        
        # 如果正在更新滑块值，则跳过
        if self.is_time_scale_updating:
            return
            
        try:
            self.is_time_scale_updating = True
            
            # 获取当前秒数并应用吸附逻辑（使用自定义吸附间隔）
            raw_seconds = float(self.time_scale.get())
            # 根据自定义间隔进行吸附
            seconds = round(raw_seconds / self.snap_interval) * self.snap_interval
            
            # 更新滑块到吸附后的位置
            self.time_scale.set(seconds)
            
            # 确保秒数不超过总秒数
            seconds = min(seconds, self.total_seconds)
            frame = int(seconds * self.fps)
            # 确保帧数不超过总帧数，并确保不小于0
            frame = max(0, min(frame, self.total_frames - 1))
            # 额外检查：确保帧数在文本框内容数组范围内
            if len(self.text_box["contents"]) > 0:
                frame = min(frame, len(self.text_box["contents"]) - 1)
            
            self.current_frame = frame
            self.current_second = seconds
            
            # 更新文本框内容显示
            self.text_content_entry.delete(0, tk.END)
            if (self.current_frame < len(self.text_box["contents"]) and 
                self.current_frame >= 0 and 
                len(self.text_box["contents"]) > 0):
                self.text_content_entry.insert(0, self.text_box["contents"][self.current_frame])
            
            # 更新持续时间显示
            self.text_duration_entry.delete(0, tk.END)
            current_duration = self.get_text_duration_at_frame(self.current_frame)
            self.text_duration_entry.insert(0, str(current_duration))
            
            # 更新时间显示 - 只显示整数秒
            self.text_second_entry.delete(0, tk.END)
            self.text_second_entry.insert(0, str(int(self.current_second)))
            
            # 重置拖动状态
            self.dragging = False
            self.drag_item = None
            self.drag_type = None
            self.drag_index = None
            self.drag_start_pos = None
            self.drag_end_pos = None
            
            # 如果有音频文件，同步音频位置（不论是否正在播放）
            if self.audio_file:
                # 检查动画是否正在播放
                is_playing = hasattr(self, 'animation_loop') and self.animation_loop.running
                
                print(f"时间轴滑块释放，同步音频到 {self.current_second:.2f} 秒")
                # 使用平滑的音频同步方式，减少杂音
                current_volume = pygame.mixer.music.get_volume()
                pygame.mixer.music.set_volume(0.0)
                pygame.mixer.music.stop()
                pygame.mixer.music.set_volume(current_volume)
                pygame.mixer.music.play(loops=0, start=self.current_second)
                
                # 更新动画循环的音频同步状态
                if hasattr(self, 'animation_loop'):
                    self.animation_loop.audio_start_time = self.root.tk.call('clock', 'milliseconds')
                    self.animation_loop.audio_started = True
                    # 重置同步检查时间
                    if hasattr(self.animation_loop, 'last_sync_check'):
                        self.animation_loop.last_sync_check = self.animation_loop.audio_start_time
                
                # 如果动画没有在播放，则暂停音频
                if not is_playing:
                    pygame.mixer.music.pause()
                    if hasattr(self, 'animation_loop'):
                        self.animation_loop.audio_started = False
            
            # 更新舞台预览
            self.update_stage_preview()
            
            # update_stage_preview 已经包含了 draw_idle()，不需要再次调用
            
        finally:
            self.is_time_scale_updating = False

    def export_animation_with_audio(self):
        """导出带音频的动画"""
        # 检查动画是否正在播放
        if hasattr(self, 'animation_loop') and self.animation_loop.running:
            messagebox.showwarning("警告", "请先停止动画播放再进行导出")
            return
            
        if not self.audio_file:
            messagebox.showwarning("警告", "请先导入音频文件")
            return
            
        try:
            # 获取导出帧率
            export_fps = int(self.export_fps_entry.get())
            if export_fps <= 0:
                raise ValueError("导出帧率必须大于0")
            
            # 创建临时目录
            temp_dir = tempfile.mkdtemp()
            
            try:
                # 创建导出目录
                export_dir = "exports"
                if not os.path.exists(export_dir):
                    os.makedirs(export_dir)
                
                # 让用户选择保存位置
                export_path = filedialog.asksaveasfilename(
                    defaultextension=".mp4",
                    initialdir=export_dir,
                    initialfile="stage_animation_with_audio.mp4",
                    filetypes=[("MP4 files", "*.mp4"), ("All files", "*.*")]
                )
                
                if not export_path:  # 用户取消选择
                    return
                
                # 创建进度条窗口
                progress_window = tk.Toplevel(self.root)
                progress_window.title("MP4带音频导出进度")
                progress_window.geometry("450x220")
                progress_window.resizable(False, False)
                progress_window.transient(self.root)
                progress_window.grab_set()
                
                # 添加UI元素
                main_label = ttk.Label(progress_window, text="正在导出带音频的MP4动画...", font=('Arial', 12, 'bold'))
                main_label.pack(pady=15)
                progress_bar = ttk.Progressbar(progress_window, length=400, mode='determinate')
                progress_bar.pack(pady=10)
                status_label = ttk.Label(progress_window, text="初始化中...", font=('Arial', 10))
                status_label.pack(pady=5)
                detail_label = ttk.Label(progress_window, text="", font=('Arial', 9))
                detail_label.pack(pady=5)
                time_label = ttk.Label(progress_window, text="", font=('Arial', 8))
                time_label.pack(pady=5)
                cancel_button = ttk.Button(progress_window, text="取消", 
                                         command=lambda: setattr(self, '_cancel_export', True))
                cancel_button.pack(pady=10)
                
                # 初始化状态
                self._cancel_export = False
                start_time = time.time()
                total_export_frames = int(self.total_seconds * export_fps)
                
                # 显示项目信息
                status_label.config(text=f"准备导出 {total_export_frames} 帧")
                detail_label.config(text=f"帧率: {export_fps} FPS | 时长: {self.total_seconds:.1f}秒 | 音频: {os.path.basename(self.audio_file)}")
                progress_window.update()
                
                # 创建线程池
                frame_queue = Queue()
                
                def render_frame_job(frame):
                    """渲染单个帧的作业"""
                    if hasattr(self, '_cancel_export') and self._cancel_export:
                        return None
                        
                    frame_path = os.path.join(temp_dir, f"frame_{frame:04d}.png")
                    
                    # 创建图形对象
                    export_fig = Figure(figsize=(10, 8), dpi=100)
                    export_ax = export_fig.add_subplot(111)
                    export_fig.patch.set_facecolor('white')
                    export_ax.set_facecolor('white')
                    
                    # 渲染帧内容，传入is_export=True
                    self.render_frame(export_ax, frame, export_fps, is_export=True)
                    
                    # 保存帧
                    export_fig.savefig(frame_path, 
                                      facecolor='white',
                                      edgecolor='none',
                                      dpi=100,
                                      pad_inches=0)
                    plt.close(export_fig)
                    return frame_path
                
                try:
                    frame_files = []
                    completed_frames = 0
                    
                    # 使用线程池并行渲染帧
                    cpu_count = os.cpu_count() or 4  # 如果cpu_count返回None，使用默认值4
                    with concurrent.futures.ThreadPoolExecutor(max_workers=min(cpu_count, 4)) as executor:
                        # 提交所有渲染任务
                        future_to_frame = {executor.submit(render_frame_job, frame): frame 
                                         for frame in range(total_export_frames)}
                        
                        # 处理完成的帧
                        for future in concurrent.futures.as_completed(future_to_frame):
                            frame = future_to_frame[future]
                            try:
                                frame_path = future.result()
                                if frame_path is None:  # 用户取消
                                    raise Exception("用户取消导出")
                                frame_files.append(frame_path)
                                
                                # 更新进度
                                completed_frames += 1
                                progress = (completed_frames / total_export_frames) * 100
                                progress_bar['value'] = progress
                                
                                # 计算预计剩余时间
                                elapsed_time = time.time() - start_time
                                if completed_frames > 0:
                                    avg_time_per_frame = elapsed_time / completed_frames
                                    remaining_frames = total_export_frames - completed_frames
                                    estimated_remaining = avg_time_per_frame * remaining_frames
                                    
                                    status_label.config(text=f"正在渲染帧 {completed_frames}/{total_export_frames}")
                                    time_label.config(text=f"已用时: {int(elapsed_time)}秒 | 预计剩余: {int(estimated_remaining)}秒")
                                
                                progress_window.update()
                                
                            except Exception as e:
                                print(f"渲染帧 {frame} 时出错: {e}")
                                raise
                    
                    # 按帧序号排序
                    frame_files.sort()
                    
                    # 更新状态
                    status_label.config(text="正在创建视频...")
                    progress_window.update()
                    
                    # 创建视频剪辑
                    video_clip = ImageSequenceClip(frame_files, fps=export_fps)
                    audio_clip = AudioFileClip(self.audio_file)
                    
                    # 确保音视频时长匹配
                    if audio_clip.duration > video_clip.duration:
                        audio_clip = audio_clip.subclipped(0, video_clip.duration)  # type: ignore
                    else:
                        video_clip = video_clip.with_duration(audio_clip.duration)  # type: ignore
                    
                    final_clip = video_clip.with_audio(audio_clip)  # type: ignore
                    
                    # 更新状态
                    status_label.config(text="正在导出最终视频...")
                    progress_window.update()
                    
                    # 使用优化的编码参数
                    cpu_count_for_encoding = os.cpu_count() or 4  # 如果cpu_count返回None，使用默认值4
                    
                    # 确保ffmpeg可用（对于打包后的exe）
                    # moviepy会自动使用imageio_ffmpeg提供的ffmpeg
                    
                    final_clip.write_videofile(
                        export_path,
                        codec='libx264',
                        audio_codec='aac',
                        fps=export_fps,
                        preset='ultrafast',  # 使用最快的编码预设
                        threads=min(cpu_count_for_encoding, 4),  # 使用多线程编码
                        bitrate='2000k',
                        audio_bitrate='128k',
                        logger=None  # 禁用详细日志输出
                    )
                    
                    # 清理资源
                    final_clip.close()
                    video_clip.close()
                    audio_clip.close()
                    
                    # 显示成功消息
                    self.log(f"✓ 带音频MP4导出成功: {os.path.basename(export_path)}", 'success')
                    
                except Exception as e:
                    raise Exception(f"导出过程中出错: {str(e)}")
                    
                finally:
                    # 关闭进度窗口
                    progress_window.destroy()
                    
            finally:
                # 清理临时文件
                shutil.rmtree(temp_dir)
                
        except Exception as e:
            messagebox.showerror("错误", f"导出失败: {str(e)}")
            print(f"导出错误详情: {str(e)}")
            traceback.print_exc()

    def render_frame(self, ax, frame, export_fps, is_export=False):
        """渲染单个帧
        Args:
            ax: matplotlib轴对象
            frame: 当前帧号
            export_fps: 导出帧率
            is_export: 是否是导出模式（影响渲染样式）
        """
        # 计算当前时间点
        current_time = frame / export_fps
        current_frame = int(current_time * self.fps)
        current_frame = min(current_frame, self.total_frames - 1)
        
        # 设置显示范围 - 调整Y轴范围以显示观众区域
        invisible_width = self.stage_width / 8  # 左右备台区域宽度
        ax.set_xlim(-self.stage_width/2 - invisible_width, self.stage_width/2 + invisible_width)
        # 计算后方备台区域高度以调整视图范围
        backstage_height = self.stage_height / 8
        ax.set_ylim(-2, self.stage_height + backstage_height + 1)  # 包含后方备台区域
        
        # 设置固定的长宽比，确保舞台和对象不会变形
        ax.set_aspect('equal', adjustable='box')
        
        # 绘制舞台边界
        stage_rect = Rectangle((-self.stage_width/2, 0), self.stage_width, self.stage_height, 
                             fill=False, color='black', linewidth=2)
        ax.add_patch(stage_rect)
        
        # 绘制舞台中线（红色虚线）
        ax.plot([0, 0], [0, self.stage_height], 'r--', linewidth=0.8, alpha=0.5)
        
        # 绘制备台区域
        invisible_width = self.stage_width / 8  # 左右备台区域宽度为舞台宽度的1/8
        
        # 左侧备台区域
        left_invisible = Rectangle((-self.stage_width/2 - invisible_width, 0), 
                                 invisible_width, self.stage_height,
                                 fill=True, color='gray', alpha=0.3)
        ax.add_patch(left_invisible)
        ax.text(-self.stage_width/2 - invisible_width/2, self.stage_height/2, '左侧\n备台区域', 
                 rotation=90, ha='center', va='center', color='gray', alpha=0.7, fontsize=12)
        
        # 右侧备台区域
        right_invisible = Rectangle((self.stage_width/2, 0), 
                                  invisible_width, self.stage_height,
                                  fill=True, color='gray', alpha=0.3)
        ax.add_patch(right_invisible)
        ax.text(self.stage_width/2 + invisible_width/2, self.stage_height/2, '右侧\n备台区域', 
                 rotation=90, ha='center', va='center', color='gray', alpha=0.7, fontsize=12)
        
        # 后方备台区域 - 连接左右两侧
        backstage_height = self.stage_height / 8  # 后方备台区域高度为舞台高度的1/8
        upper_backstage = Rectangle((-self.stage_width/2 - invisible_width, self.stage_height), 
                                   self.stage_width + 2 * invisible_width, backstage_height,
                                   fill=True, color='gray', alpha=0.3)
        ax.add_patch(upper_backstage)
        ax.text(0, self.stage_height + backstage_height/2, '后方备台区域', 
                 ha='center', va='center', color='gray', alpha=0.7, fontsize=12)
        
        # 添加观众区域标识 - 调整位置和样式
        ax.text(0, -1, '观众区域', ha='center', va='center', 
                color='gray', alpha=0.7, fontsize=12,
                bbox=dict(facecolor='white', alpha=0.3, edgecolor='gray', pad=3))
        
        # 绘制演员和道具
        self.render_actors(ax, current_frame, is_export)
        self.render_props(ax, current_frame, is_export)
        
        # 绘制文本框 - 放置在后方备台区域上方且不重合
        if (current_frame < len(self.text_box["contents"]) and 
            current_frame >= 0 and 
            len(self.text_box["contents"]) > 0):
            text_content = self.text_box["contents"][current_frame]
            if text_content:
                backstage_height = self.stage_height / 8  # 后方备台区域高度
                text_y_position = self.stage_height + backstage_height + 0.5  # 在后方备台区域上方0.5单位
                ax.text(0, text_y_position,
                       text_content,
                       ha='center', va='center',
                       fontsize=self.text_box["font_size"],
                       color='black',
                       bbox=dict(facecolor='white', alpha=0.7, edgecolor='black', pad=5))
        
        # 设置标题
        ax.set_title(f'舞台动画 - 时间: {current_time:.1f}秒', fontsize=14, weight='bold', pad=20)
        
        # 隐藏坐标轴
        ax.set_axis_off()

    def render_actors(self, ax, current_frame, is_export=False):
        """渲染演员
        Args:
            ax: matplotlib轴对象
            current_frame: 当前帧号
            is_export: 是否是导出模式（影响渲染样式）
        """
        for actor in self.actors:
            # 获取当前位置
            if actor["keyframes"]:
                prev_frame = max([f for f in actor["keyframes"] if f <= current_frame], default=None)
                next_frame = min([f for f in actor["keyframes"] if f > current_frame], default=None)
                
                if prev_frame is not None:
                    if next_frame is not None:
                        pos = actor["positions"][current_frame]
                    else:
                        pos = actor["positions"][prev_frame]
                else:
                    pos = actor["positions"][0]
            else:
                pos = actor["positions"][0]
            
            # 获取颜色，如果没有颜色属性则使用默认颜色
            color = actor.get("color", "blue")
            # 获取字号，如果没有字号属性则使用默认字号
            font_size = actor.get("font_size", 10)
            
            # 检查位置是否在可见区域内（包括舞台和备台区域）
            if self.is_position_in_visible_area(pos):
                if actor["shape"] == "circle":
                    circle = Circle((pos[0], pos[1]), actor["size"], 
                                 fill=False,  # 不填充
                                 color=color, 
                                 linewidth=2)
                    ax.add_patch(circle)
                    ax.text(pos[0], pos[1], actor["name"], 
                          ha='center', va='center', 
                          color=color,  # 文字颜色与轮廓一致
                          fontsize=font_size, 
                          weight='bold')
                elif actor["shape"] == "square":
                    rect = Rectangle((pos[0]-actor["size"]/2, pos[1]-actor["size"]/2),
                                   actor["size"], actor["size"], 
                                   fill=False,  # 不填充
                                   color=color, 
                                   linewidth=2)
                    ax.add_patch(rect)
                    ax.text(pos[0], pos[1], actor["name"], 
                          ha='center', va='center', 
                          color=color,  # 文字颜色与轮廓一致
                          fontsize=font_size, 
                          weight='bold')
                elif actor["shape"] == "triangle":
                    triangle = Polygon([(pos[0], pos[1]+actor["size"]),
                                      (pos[0]-actor["size"], pos[1]-actor["size"]),
                                      (pos[0]+actor["size"], pos[1]-actor["size"])], 
                                     fill=False,  # 不填充
                                     color=color, 
                                     linewidth=2)
                    ax.add_patch(triangle)
                    ax.text(pos[0], pos[1], actor["name"], 
                          ha='center', va='center', 
                          color=color,  # 文字颜色与轮廓一致
                          fontsize=font_size, 
                          weight='bold')
        
        # 绘制所有道具
        for prop in self.props:
            # 获取当前位置
            if prop["keyframes"]:
                prev_frame = max([f for f in prop["keyframes"] if f <= current_frame], default=None)
                next_frame = min([f for f in prop["keyframes"] if f > current_frame], default=None)
                
                if prev_frame is not None:
                    if next_frame is not None:
                        pos = prop["positions"][current_frame]
                    else:
                        pos = prop["positions"][prev_frame]
                else:
                    pos = prop["positions"][0]
            else:
                pos = prop["positions"][0]
            
            # 获取颜色，如果没有颜色属性则使用默认颜色
            color = prop.get("color", "red")
            # 获取字号，如果没有字号属性则使用默认字号
            font_size = prop.get("font_size", 10)
            
            # 检查位置是否在舞台区域内
            if self.is_position_in_stage(pos):
                if prop["shape"] == "rectangle":
                    rect = Rectangle((pos[0]-prop["width"]/2, pos[1]-prop["height"]/2),
                                   prop["width"], prop["height"], 
                                   fill=False,  # 不填充
                                   color=color, 
                                   linewidth=2)
                    ax.add_patch(rect)
                    ax.text(pos[0], pos[1], prop["name"], 
                          ha='center', va='center', 
                          color=color,  # 文字颜色与轮廓一致
                          fontsize=font_size, 
                          weight='bold')
                elif prop["shape"] == "circle":
                    circle = Circle((pos[0], pos[1]), prop["width"]/2, 
                                 fill=False,  # 不填充
                                 color=color, 
                                 linewidth=2)
                    ax.add_patch(circle)
                    ax.text(pos[0], pos[1], prop["name"], 
                          ha='center', va='center', 
                          color=color,  # 文字颜色与轮廓一致
                          fontsize=font_size, 
                          weight='bold')
                elif prop["shape"] == "triangle":
                    triangle = Polygon([(pos[0], pos[1]+prop["height"]/2),
                                      (pos[0]-prop["width"]/2, pos[1]-prop["height"]/2),
                                      (pos[0]+prop["width"]/2, pos[1]-prop["height"]/2)], 
                                     fill=False,  # 不填充
                                     color=color, 
                                     linewidth=2)
                    ax.add_patch(triangle)
                    ax.text(pos[0], pos[1], prop["name"], 
                          ha='center', va='center', 
                          color=color,  # 文字颜色与轮廓一致
                          fontsize=font_size, 
                          weight='bold')
    
    def render_props(self, ax, current_frame, is_export=False):
        """渲染道具
        Args:
            ax: matplotlib轴对象
            current_frame: 当前帧号
            is_export: 是否是导出模式（影响渲染样式）
        """
        for prop in self.props:
            # 获取当前位置
            if prop["keyframes"]:
                prev_frame = max([f for f in prop["keyframes"] if f <= current_frame], default=None)
                next_frame = min([f for f in prop["keyframes"] if f > current_frame], default=None)
                
                if prev_frame is not None:
                    if next_frame is not None:
                        pos = prop["positions"][current_frame]
                    else:
                        pos = prop["positions"][prev_frame]
                else:
                    pos = prop["positions"][0]
            else:
                pos = prop["positions"][0]
            
            # 获取颜色，如果没有颜色属性则使用默认颜色
            color = prop.get("color", "red")
            # 获取字号，如果没有字号属性则使用默认字号
            font_size = prop.get("font_size", 10)
            
            # 检查位置是否在可见区域内（包括舞台和备台区域）
            if self.is_position_in_visible_area(pos):
                if prop["shape"] == "rectangle":
                    rect = Rectangle((pos[0]-prop["width"]/2, pos[1]-prop["height"]/2),
                                   prop["width"], prop["height"], 
                                   fill=False,  # 不填充
                                   color=color, 
                                   linewidth=2)
                    ax.add_patch(rect)
                    ax.text(pos[0], pos[1], prop["name"], 
                          ha='center', va='center', 
                          color=color,  # 文字颜色与轮廓一致
                          fontsize=font_size, 
                          weight='bold')
                elif prop["shape"] == "circle":
                    circle = Circle((pos[0], pos[1]), prop["width"]/2, 
                                 fill=False,  # 不填充
                                 color=color, 
                                 linewidth=2)
                    ax.add_patch(circle)
                    ax.text(pos[0], pos[1], prop["name"], 
                          ha='center', va='center', 
                          color=color,  # 文字颜色与轮廓一致
                          fontsize=font_size, 
                          weight='bold')
                elif prop["shape"] == "triangle":
                    triangle = Polygon([(pos[0], pos[1]+prop["height"]/2),
                                      (pos[0]-prop["width"]/2, pos[1]-prop["height"]/2),
                                      (pos[0]+prop["width"]/2, pos[1]-prop["height"]/2)], 
                                     fill=False,  # 不填充
                                     color=color, 
                                     linewidth=2)
                    ax.add_patch(triangle)
                    ax.text(pos[0], pos[1], prop["name"], 
                          ha='center', va='center', 
                          color=color,  # 文字颜色与轮廓一致
                          fontsize=font_size, 
                          weight='bold')
    
    def is_position_in_stage(self, pos):
        """检查位置是否在舞台区域内"""
        x, y = pos
        return (-self.stage_width/2 <= x <= self.stage_width/2) and (0 <= y <= self.stage_height)
    
    def is_position_in_visible_area(self, pos):
        """检查位置是否在可见区域内（包括舞台和备台区域）"""
        x, y = pos
        invisible_width = self.stage_width / 8  # 左右备台区域宽度
        backstage_height = self.stage_height / 8  # 后方备台区域高度
        
        # 检查X轴范围：包括左右备台区域
        x_in_range = (-self.stage_width/2 - invisible_width <= x <= self.stage_width/2 + invisible_width)
        
        # 检查Y轴范围：包括舞台和后方备台区域
        y_in_range = (0 <= y <= self.stage_height + backstage_height)
        
        return x_in_range and y_in_range

    def on_volume_change(self, value):
        """处理音量变化事件"""
        self.audio_volume = float(value) / 100
        pygame.mixer.music.set_volume(self.audio_volume)

    def on_ruler_toggle(self):
        """处理标尺显示切换事件"""
        if self.ruler_enabled.get():
            # 显示标尺容器
            self.ruler_container.pack(fill=tk.X, padx=5, pady=2, before=self.time_scale)
            # 创建标尺按钮
            self.update_custom_ruler()
            print("✅ 标尺显示已启用")
        else:
            # 隐藏标尺容器
            self.ruler_container.pack_forget()
            # 清除标尺按钮
            self.clear_custom_ruler()
            print("❌ 标尺显示已关闭")
    
    def on_snap_interval_change(self, event=None):
        """处理滑块吸附间隔变化事件"""
        try:
            interval = float(self.snap_interval_entry.get())
            # 四舍五入到小数点后1位
            interval = round(interval, 1)
            
            if interval >= 0.1:  # 确保间隔大于等于0.1秒
                self.snap_interval = interval
                # 更新输入框显示为规范化的值（小数点后1位）
                self.snap_interval_entry.delete(0, tk.END)
                self.snap_interval_entry.insert(0, f"{interval:.1f}")
                print(f"滑块吸附间隔更新为: {interval}秒")
            else:
                # 如果输入不合法（小于0.1秒），恢复到之前的值
                self.snap_interval_entry.delete(0, tk.END)
                self.snap_interval_entry.insert(0, f"{self.snap_interval:.1f}")
                messagebox.showwarning("警告", "滑块吸附间隔不能小于0.1秒")
        except ValueError:
            # 如果输入不是数字，恢复到之前的值
            self.snap_interval_entry.delete(0, tk.END)
            self.snap_interval_entry.insert(0, f"{self.snap_interval:.1f}")
    
    def on_custom_interval_change(self, event=None):
        """处理自定义间隔变化事件"""
        try:
            interval = int(self.custom_interval_entry.get())
            if interval >= 1:  # 确保间隔大于等于1秒
                self.custom_interval = interval
                if self.ruler_enabled.get():
                    self.update_custom_ruler()
                print(f"标尺间隔更新为: {interval}秒")
            else:
                # 如果输入不合法，恢复到之前的值
                self.custom_interval_entry.delete(0, tk.END)
                self.custom_interval_entry.insert(0, str(self.custom_interval))
        except ValueError:
            # 如果输入不是数字，恢复到之前的值
            self.custom_interval_entry.delete(0, tk.END)
            self.custom_interval_entry.insert(0, str(self.custom_interval))
    
    def update_custom_ruler(self):
        """更新自定义模式的标尺显示"""
        # 清除现有标尺
        self.clear_custom_ruler()
        
        # 创建新的标尺按钮
        interval = self.custom_interval
        total_time = int(self.total_seconds)
        
        # 计算标尺按钮的数量和位置
        ruler_times = []
        for t in range(0, total_time + 1, interval):
            if t <= total_time:
                ruler_times.append(t)
        
        # 如果最后一个标尺不是总时长，添加总时长标尺
        if ruler_times and ruler_times[-1] != total_time:
            ruler_times.append(total_time)
        
        # 创建标尺按钮
        for i, time_val in enumerate(ruler_times):
            btn = ttk.Button(self.ruler_frame, text=f"{time_val}s", width=6,
                           command=lambda t=time_val: self.jump_to_time(t))
            btn.pack(side=tk.LEFT, padx=1)
            self.ruler_buttons.append(btn)
        
        print(f"创建了 {len(self.ruler_buttons)} 个标尺按钮，间隔: {interval}秒")
    
    def clear_custom_ruler(self):
        """清除自定义标尺"""
        for btn in self.ruler_buttons:
            btn.destroy()
        self.ruler_buttons.clear()
    
    def jump_to_time(self, target_time):
        """跳转到指定时间"""
        print(f"跳转到时间: {target_time}秒")
        
        # 更新时间轴滑块
        self.time_scale.set(target_time)
        
        # 手动触发时间变化事件
        self.on_time_scale_change(str(target_time))
    


if __name__ == "__main__":
    root = tk.Tk()
    app = StageAnimationTool(root)
    root.mainloop() 